structure tigersimpleregalloc :> tigersimpleregalloc =
struct
	structure frame = tigerframe
	open tigerassem
  open tigergraph
  open tigerliveness
  
  structure Table = Splaymap
  structure Set = Splayset
	
  val moveList : (tigertemp.temp, tigergraph.node Set.set) Table.dict ref = ref (Table.mkDict String.compare)
  val worklistMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val adjSet : (tigertemp.temp * tigertemp.temp) Set.set ref = ref (Set.empty (fn ((a,b),(c,d))  => if (a,b) = (c,d) then EQUAL else String.compare (a,c)))
  val adjList : (tigertemp.temp, tigertemp.temp Set.set) Table.dict ref = ref (Table.mkDict String.compare)
  val degree : (tigertemp.temp, int) Table.dict ref = ref (Table.mkDict String.compare)
  val precolored : tigerframe.register list ref = ref tigerframe.allRegs
  val initial : tigertemp.temp Set.set ref = ref  (Set.empty String.compare)
  val spillWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
  val colorCount = length tigerframe.allRegs
  val activeMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val freezeWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
	val simplifyWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
	val selectStack : tigertemp.temp list ref = ref []
	val coalescedNodes : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
	val useDef : (tigergraph.node, tigertemp.temp * tigertemp.temp) Table.dict ref = ref (Table.mkDict tigergraph.compareNodes)
  


	fun livenessAnalysis (body : instr list) = #1 (tigermg.instr2graph body)

	fun updateTable(t,n,x) =
		t := Table.insert(!t, n, Set.add(Table.find(!t, n), x))

	fun updateSet(s,x) =
		s := Set.add(!s, x)

	fun updateTableInt(t,n,f) =
		t := Table.insert(!t, n, f (Table.find(!t, n)))

	fun removeElemTempSet(s,x) =
		s := Set.difference(!s, Set.singleton String.compare x)

	fun removeElemNodeSet(s,x) =
		s := Set.difference(!s, Set.singleton tigergraph.compareNodes x)

	fun listToSet(l) =
		Set.addList(Set.empty String.compare, !l)

	fun push(x,xs) = x::(!xs)
	
	(*FALTA TRATAR EL TEMA DE CUANDO XS ES VACIO*)
	fun pop(xs) = hd(!xs)

	fun addEdge (u,v) =
		if not(Set.member (!adjSet, (u,v))) andalso not(u = v)
		then
			let val _ = adjSet := Set.add (Set.add (!adjSet, (u,v)), (v,u))
				  val _ = if not(List.exists (fn x => x = u) (!precolored))
				          then (updateTable(adjList,u,v);				          		
				          		  updateTableInt (degree, u, fn x => x+1);
				          		  updateSet(initial, u))
				          else ()
				  val _ = if not(List.exists (fn x => x = v) (!precolored))
				          then (updateTable(adjList,v,u);
				          		  updateTableInt (degree, u, fn x => x+1);
				          		  updateSet(initial, v))
				          else ()
			in () end
		else ()

	fun build (flowg : tigerflow.flowgraph) =
		let val g      = #control flowg
			  val moves  = #ismove flowg
		    val instrs = tigergraph.nodes g
			  val louts  = tigerliveness.liveOuts flowg
				fun buildAux i = 
			  	let val live = ref (T.find (louts, i))
			  			val useSet = T.find (#use flowg, i)
			  			val defSet = T.find (#def flowg, i)
			  			val _ = if T.find (moves, i)
								  		then
								  			let
								  				val _ = live := Set.difference (!live, useSet)
								  				val _ = Set.app (fn d => Set.app (fn u => useDef := Table.insert(!useDef, i, (d,u))) useSet) defSet
								  			in
								  				Set.app (fn x => updateTable(moveList, x, i)) (Set.union (defSet,useSet));
								  				updateSet(worklistMoves, i)
								  			end
								  		else
								  			()
							val _ = live := Set.union (!live, defSet)

			    in
			     	Set.app (fn a =>
	                   	Set.app (fn b => addEdge (a,b)) (!live)
	                  ) defSet
			  	end
		in
			app buildAux instrs
		end

	fun nodeMoves(n) =
		Set.intersection(Table.find(!moveList, n), Set.union(!activeMoves, !worklistMoves))
	
	fun moveRelated(n) =
		not(Set.isEmpty(nodeMoves(n)))

	fun makeWorkList () =
		let
			fun makeWorkL x =
				let
					val _ = removeElemTempSet(initial, x)
				in
					if Table.find(!degree, x) >= colorCount
					then
						updateSet(spillWorklist, x)
					else 
						if moveRelated(x)
						then updateSet(freezeWorklist, x)
						else updateSet(simplifyWorklist, x)
				end
		in
			Set.app makeWorkL (!initial)
		end

	fun adjacent(n) =
		Set.difference(Table.find(!adjList, n), Set.union(listToSet(selectStack), !coalescedNodes))

	fun enableMoves(nodes) =
		let fun enableMovesAux m =
			    if Set.member (!activeMoves, m)
			    then
			    	(removeElemNodeSet(activeMoves, m);
			    	 updateSet(worklistMoves, m))
			    else
			    	()
		in
			Set.app (fn n => Set.app (fn m => enableMovesAux m) (nodeMoves(n))) nodes
		end 

	fun decrementDegree(m) =
		let val d = Table.find(!degree, m)
			  val _ = updateTableInt(degree, m, fn _ => d-1)
		in
			if d = colorCount
			then
				(enableMoves(Set.add(adjacent(m) ,m));
				 removeElemTempSet(spillWorklist, m);
				 if moveRelated(m)
				 then
				   updateSet(freezeWorklist, m)
				 else
				   updateSet(simplifyWorklist, m))
			else
				()
		end

	fun simplify() =
		case Set.find (fn _ => true) (!simplifyWorklist) of
		  SOME s => 
			let val _ = removeElemTempSet(simplifyWorklist, s)
				  val _ = push(s,selectStack)
			in
				Set.app decrementDegree (adjacent(s))
			end
		| NONE => ()

	fun simpleregalloc (frm:frame.frame) (body:instr list) =
	let
		(* COMPLETAR: Temporarios que ya tienen color asignado (p.ej, el temporario que representa a rax) *)
		val precolored = ["a", "b", "c", "d", "e", "f"]
		(* COMPLETAR: Temporarios que se pueden usar (p.ej, el temporario que representa a rax. Diferencia con precolored: el temporario que representa a rbp no se puede usar) *)
		val asignables = ["b", "c", "d", "e", "f"]
		(* COMPLETAR: movaMem crea una instrucción que mueve un temporario a memoria. movaTemp, de memoria a un temporario.*)
		fun movaMem(temp, mempos) =
			let
				val desp = if mempos<0 then " - " ^ Int.toString(~mempos) else if mempos>0 then " + " ^ Int.toString(mempos) else ""
			in
				OPER {assem="mov `s0 M(a" ^ desp ^ ")", src=[temp], dst=[], jump=NONE}
			end
		fun movaTemp(mempos, temp) =
			let
				val desp = if mempos<0 then " - " ^ Int.toString(~mempos) else if mempos>0 then " + " ^ Int.toString(mempos) else ""
			in
				OPER {assem="mov M(a" ^ desp ^ ") `d0", src=[], dst=[temp], jump=NONE}
			end
		val temps =
			let
				val tempList = 
					let
						fun f (OPER r, tmplist) = List.concat [#dst r, #src r, tmplist]
						| f (LABEL _, tmplist) = tmplist
						(*| f (MOVE r, tmplist) = (#dst r)::(#src r)::tmplist*)
					in
						List.foldr f [] body
					end
				val s = Splayset.addList(Splayset.empty String.compare, tempList)
				val precoloredSet = Splayset.addList(Splayset.empty String.compare, precolored)
			in
				Splayset.listItems(Splayset.difference(s, precoloredSet))
			end

		val accesses = map (fn T => let val frame.InFrame n = frame.allocLocal frm true in (T, n) end) temps
		fun getFramePos T =
			let
				fun gfp T [] = raise Fail("Temporario no encontrado: "^T)
				| gfp T ((a,b)::xs) = if a=T then b else gfp T xs
			in
				gfp T accesses
			end

		fun rewriteInstr (OPER {assem, dst, src, jump}) =
			let
				val eset = Splayset.empty String.compare
				val precoloredSet = Splayset.addList(eset, precolored)
				val asignablesSet = Splayset.addList(eset, asignables)
				val dstset = Splayset.addList(eset, dst)
				val srcset = Splayset.addList(eset, src)
				val colores = Splayset.listItems(Splayset.difference(asignablesSet, Splayset.union(dstset, srcset)))
				val uncolored = Splayset.listItems(Splayset.difference(Splayset.union(dstset, srcset), precoloredSet))

				val N = length(uncolored)
				val tempcols = ListPair.zip(uncolored, List.take(colores, N))
				fun getTempCol T =
				let
					fun gtc T [] = if Splayset.member(precoloredSet, T) then T else raise Fail("Temporario no encontrado: "^T)
					| gtc T ((a,b)::xs) = if a=T then b else gtc T xs
				in
					gtc T tempcols
				end

				val (prevMovs, posMovs) =
				let
					fun mkgetMov T = movaTemp(getFramePos T, getTempCol T)
					fun mksetMov T = movaMem(getTempCol T, getFramePos T)
					fun filterPC T = not(Splayset.member(precoloredSet, T))
				in
					(map mkgetMov (List.filter filterPC src), map mksetMov (List.filter filterPC dst))
				end
				val newdst = map getTempCol dst
				val newsrc = map getTempCol src
				val newinstr = OPER {assem=assem, dst=newdst, src=newsrc, jump=jump}
			in
				List.concat [prevMovs, [newinstr], posMovs]
			end
		  | rewriteInstr (LABEL l) = [LABEL l]
		  | rewriteInstr (MOVE {assem, dst, src}) =
			let
				val precoloredSet = Splayset.addList(Splayset.empty String.compare, precolored)
			in
			(*	if Splayset.member(precoloredSet, dst) andalso Splayset.member(precoloredSet, src) then [OPER {assem=assem, dst=[dst], src=[src], jump=NONE}]
				else if Splayset.member(precoloredSet, dst) then [movaTemp(getFramePos src, dst)]
				else if Splayset.member(precoloredSet, src) then [movaMem(src, getFramePos dst)]
				else
					let
						val color = hd(asignables)
					in
						[movaTemp(getFramePos src, color), movaMem(color, getFramePos dst)]
					end*) []
			end
	in
		List.concat (map rewriteInstr body)
	end
end
