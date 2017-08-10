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
  val precolored : tigerframe.register Set.set = Set.addList((Set.empty String.compare), tigerframe.allRegs)
  val initial : tigertemp.temp Set.set ref = ref  (Set.empty String.compare)
  val spillWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
  val colorCount = length tigerframe.allRegs
  val activeMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val freezeWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
	val simplifyWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
	val selectStack : tigertemp.temp list ref = ref []
	val coalescedNodes : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
	val movesPair : (tigergraph.node, tigertemp.temp * tigertemp.temp) Table.dict ref = ref (Table.mkDict tigergraph.compareNodes)
  val coalescedMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val constrainedMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val alias : (tigertemp.temp, tigertemp.temp) Table.dict ref = ref (Table.mkDict String.compare)
  val frozenMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val coloredNodes : tigerframe.register Set.set ref = ref (Set.empty String.compare)
  val color : (tigertemp.temp, int) Table.dict ref = ref (Table.mkDict String.compare)
	val spilledNodes : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
  


	fun livenessAnalysis (body : instr list) = #1 (tigermg.instr2graph body)

	fun getTableValue(t,x) = Table.find(!t, x)
	
	fun updateTable(t,n,f) =
		t := Table.insert(!t, n, f (getTableValue(t, n)))

	fun updateSetTable(t,n,x) =
		updateTable(t,n, fn y => Set.add(y, x))
		
	fun updateSet(s,x) =
		s := Set.add(!s, x)

	fun removeElemTempSet(s,x) =
		s := Set.difference(!s, Set.singleton String.compare x)

	fun removeElemNodeSet(s,x) =
		s := Set.difference(!s, Set.singleton tigergraph.compareNodes x)

	fun removeElemIntSet(s,x) =
		s := Set.difference(!s, Set.singleton Int.compare x)

	fun listToSet(l) =
		Set.addList(Set.empty String.compare, !l)

	fun push(x,xs) = x::(!xs)
	
	(*FALTA TRATAR EL TEMA DE CUANDO XS ES VACIO*)
	fun pop(xs) = hd(!xs)

	fun inSet(x,s) = Set.member(!s, x)

	fun inSetNoRef(x,s) = Set.member(s, x)

	fun takeElem(s) = Set.find (fn _ => true) (!s)


	fun addEdge (u,v) =
		if not(inSet((u,v), adjSet)) andalso not(u = v)
		then
			let val _ = adjSet := Set.add (Set.add (!adjSet, (u,v)), (v,u))
				  val _ = if not(inSetNoRef(u, precolored))
				          then (updateSetTable(adjList,u,v);				          		
				          		  updateTable (degree, u, fn x => x+1);
				          		  updateSet(initial, u))
				          else ()
				  val _ = if not(inSetNoRef(v, precolored))
				          then (updateSetTable(adjList,v,u);
				          		  updateTable (degree, u, fn x => x+1);
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
								  				val _ = Set.app (fn d => Set.app (fn u => movesPair := Table.insert(!movesPair, i, (d,u))) useSet) defSet
								  			in
								  				Set.app (fn x => updateSetTable(moveList, x, i)) (Set.union (defSet,useSet));
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
		Set.intersection(getTableValue(moveList, n), Set.union(!activeMoves, !worklistMoves))
	
	fun moveRelated(n) =
		not(Set.isEmpty(nodeMoves(n)))

	fun makeWorkList () =
		let
			fun makeWorkL x =
				let
					val _ = removeElemTempSet(initial, x)
				in
					if getTableValue(degree, x) >= colorCount
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
		Set.difference(getTableValue(adjList, n), Set.union(listToSet(selectStack), !coalescedNodes))

	fun enableMoves(nodes) =
		let fun enableMovesAux m =
			    if inSet(m, activeMoves)
			    then
			    	(removeElemNodeSet(activeMoves, m);
			    	 updateSet(worklistMoves, m))
			    else
			    	()
		in
			Set.app (fn n => Set.app (fn m => enableMovesAux m) (nodeMoves(n))) nodes
		end 

	fun decrementDegree(m) =
		let val d = getTableValue(degree, m)
			  val _ = updateTable(degree, m, fn _ => d-1)
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
		case takeElem(simplifyWorklist) of
		  SOME s => 
			let val _ = removeElemTempSet(simplifyWorklist, s)
				  val _ = push(s,selectStack)
			in
				Set.app decrementDegree (adjacent(s))
			end
		| NONE => ()

	fun addWorkList(u) =
		if not(inSetNoRef(u, precolored)) andalso not(moveRelated(u)) andalso (getTableValue(degree, u) < colorCount)
		then
			(removeElemTempSet(freezeWorklist, u);
			 updateSet(simplifyWorklist, u))
		else
			()

	fun ok(t,r) =
		getTableValue(degree, t) < colorCount orelse inSetNoRef(t, precolored) orelse inSet((t,r), adjSet)

	fun conservative(nodes) =
		let val k = ref 0
			  val _ = Set.app (fn n => if getTableValue(degree, n) >= colorCount then k := !k + 1 else ()) nodes
		in !k < colorCount
		end

	fun getAlias(n) =
		if inSet(n, coalescedNodes)
		then
			getAlias(getTableValue(alias, n))
		else
			n

	fun combine(u,v) =
		let val _ = if inSet(v, freezeWorklist)
		            then
		            	removeElemTempSet(freezeWorklist, v)
		            else
		            	removeElemTempSet(spillWorklist, v)
		    val _ = updateSet(coalescedNodes, v)
		    val _ = updateTable(alias, v, fn _ => u)
		    val _ = updateTable(moveList, u, fn x => Set.union(x, getTableValue(moveList, v)))
		    val _ = enableMoves(Set.singleton String.compare v)
		    val _ = Set.app (fn t => (addEdge(t,u); decrementDegree(t))) (adjacent(v))
		in
			if getTableValue(degree, u) >= colorCount andalso inSet(u, freezeWorklist)
			then
				(removeElemTempSet(freezeWorklist, u);
				 updateSet(spillWorklist, u))
			else
				()
		end

	fun coalesce() =
		case takeElem(worklistMoves) of
			SOME m =>  
			  let val (x,y) = getTableValue(movesPair, m)
		    		val (x,y) = (getAlias(x), getAlias(y))
		    		val (u,v) = if inSetNoRef(y, precolored) then (y,x) else (x,y)
		    		val _ = removeElemNodeSet(worklistMoves,m)
		    in
		    	if u = v
		    	then
		    		(updateSet(coalescedMoves, m);
		    		 addWorkList(u))
		    	else
		    		if inSetNoRef(v, precolored) orelse inSet((u,v), adjSet)
		    		then
		    			(updateSet(constrainedMoves, m);
		    			 addWorkList(u);
		    			 addWorkList(v))
		    		else
		    			if (inSetNoRef(u, precolored) andalso (Set.foldl (fn (x,r) => ok(x,u) andalso r) true (adjacent(v))))
		    			   orelse (not(inSetNoRef(u, precolored)) andalso conservative(Set.union(adjacent(u), adjacent(v))))
		    			then
		    				(updateSet(coalescedMoves, m);
		    				 combine(u, v);
		    				 addWorkList(u))
		    			else
		    				updateSet(activeMoves, m)
		    end
		| NONE => ()

	fun freezeMoves(u) =
		let fun aux(m) =
			let val (x,y) = getTableValue(movesPair, m)
				  val v = if getAlias(y) = getAlias(u) then getAlias(x) else getAlias(y)
				  val _ = removeElemNodeSet(activeMoves, m)
				  val _ = updateSet(frozenMoves, m)
			in 
				if Set.isEmpty(nodeMoves(v)) andalso getTableValue(degree, v) < colorCount
				then
					(removeElemTempSet(freezeWorklist, v);
					 updateSet(simplifyWorklist, u))
				else
					()
			end
		in Set.app aux (nodeMoves(u))
		end

	fun freeze() =
		case takeElem(freezeWorklist) of
			SOME u => (removeElemTempSet(freezeWorklist, u);
				         updateSet(simplifyWorklist, u);
				         freezeMoves(u))
		| NONE => ()

	fun selectSpill() =
		case takeElem(spillWorklist) of
			SOME m => (removeElemTempSet(spillWorklist, m);
				         updateSet(spillWorklist, m);
				         freezeMoves(m))
		| NONE => ()

	fun assignColors() =
		((while not(null(!selectStack)) do
							let val n = pop(selectStack)
								  fun createList(0) = []
								  	| createList(k) = (colorCount - k)::(createList(k-1))
							    val okColors = ref (Set.addList((Set.empty Int.compare), createList(colorCount)))
							    fun aux(w) =
							    	if Set.member(Set.union(!coloredNodes, precolored), getAlias(w))
							    	then
							    		removeElemIntSet(okColors, getTableValue(color, getAlias(w)))
							    	else
							    		()
							    val _ = Set.app aux (getTableValue(adjList, n))
							in
								if Set.isEmpty(!okColors)
								then
									updateSet(spilledNodes, n)
								else
									(updateSet(coloredNodes, n);
									 case takeElem(okColors) of
									   SOME c => updateTable(color, n, fn _ => c)
									 | NONE => ())
							end);
				Set.app (fn n => updateTable(color, n, fn _ => getTableValue(color, getAlias(n)))) (!coalescedNodes))


	fun simpleregalloc (frm:frame.frame) (body:instr list) =
	let
		(* COMPLETAR: Temporarios que ya tienen color asignado (p.ej, el temporario que representa a rax) *)
		val precolored = tigerframe.allRegs
		(* COMPLETAR: Temporarios que se pueden usar (p.ej, el temporario que representa a rax. Diferencia con precolored: el temporario que representa a rbp no se puede usar) *)
		val asignables = ["r4","r5","r6","r7","r8","r9","r10"]
		

		(* COMPLETAR: movaMem crea una instrucción que mueve un temporario a memoria. movaTemp, de memoria a un temporario.*)
		fun movaMem(temp, mempos, dirTemp) =
			let
				val desp = if mempos<0 then " -" ^ Int.toString(~mempos) else if mempos>=0 then Int.toString(mempos) else ""
			in
				OPER {assem="ldr 'd0, =" ^ desp ^ "\n" ^ "str 's0, [fp,'d0]\n", src=[temp], dst=[dirTemp], jump=NONE}
			end
		fun movaTemp(mempos, temp, dirTemp) =
			let
				val desp = if mempos<0 then " -" ^ Int.toString(~mempos) else if mempos>=0 then Int.toString(mempos) else ""
			in
				OPER {assem="ldr 'd0, =" ^ desp ^ "\n" ^ "ldr 'd1, [fp,'d0]\n", src=[], dst=[dirTemp, temp], jump=NONE}
			end
		
		(* temps = {todos los temporarios de todas las instrucciones} / {temporarios precoloreados} *)
		val temps =
			let
				val tempList = 
					let
						fun f (OPER r, tmplist) = List.concat [#dst r, #src r, tmplist]
						  | f (LABEL _, tmplist) = tmplist
						  | f (MOVE r, tmplist) = List.concat [#dst r, #src r, tmplist]
					in
						List.foldr f [] body
					end
				val s = Splayset.addList(Splayset.empty String.compare, tempList)
				val precoloredSet = Splayset.addList(Splayset.empty String.compare, precolored)
			in
				Splayset.listItems(Splayset.difference(s, precoloredSet))
			end

		val accesses = map (fn T => let val frame.InFrame n = frame.allocLocal frm true
		                                (*val _ =  print("Accesses: "^ T ^ " --- " ^ Int.toString(n) ^ "\n")*)
		                            in (T, n) end) temps
		fun getFramePos T =
			let
				fun gfp T [] = raise Fail("Temporario no encontrado: "^T)
				  | gfp T ((a,b)::xs) = if a = T then b else gfp T xs
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
				val auxTemp = List.nth(colores, N)
				fun getTempCol T =
				let
					fun gtc T [] = if Splayset.member(precoloredSet, T) then T else raise Fail("Temporario no encontrado: "^T)
					  | gtc T ((a,b)::xs) = if a = T then b else gtc T xs
				in
					gtc T tempcols
				end

				val (prevMovs, posMovs) =
				let
					fun mkgetMov T = movaTemp(getFramePos T, getTempCol T, auxTemp)
					fun mksetMov T = movaMem(getTempCol T, getFramePos T, auxTemp)
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
		  | rewriteInstr (MOVE {assem, dst=[dst], src=[src]}) =
			  let
			  	val eset = Splayset.empty String.compare
					val asignablesSet = Splayset.addList(eset, asignables)
					val dstset = Splayset.addList(eset, [dst])
					val srcset = Splayset.addList(eset, [src])
					val colores = Splayset.listItems(Splayset.difference(asignablesSet, Splayset.union(dstset, srcset)))
			  	val precoloredSet = Splayset.addList(Splayset.empty String.compare, precolored)
			  	val auxTemp = hd(colores)
			  in
			  	if Splayset.member(precoloredSet, dst) andalso Splayset.member(precoloredSet, src) then [OPER {assem=assem, dst=[dst], src=[src], jump=NONE}]
			  	else if Splayset.member(precoloredSet, dst) then [movaTemp(getFramePos src, dst, auxTemp)]
			  	else if Splayset.member(precoloredSet, src) then [movaMem(src, getFramePos dst, auxTemp)]
			  	else
			  		let
			  			val color = List.nth(asignables, 1)
			  		in
			  			[movaTemp(getFramePos src, color, auxTemp), movaMem(color, getFramePos dst, auxTemp)]
			  		end
				end
		  | rewriteInstr (MOVE _) = raise Fail("Move con más de un src o dst.")
	in
		List.concat (map rewriteInstr body)
	end
end
