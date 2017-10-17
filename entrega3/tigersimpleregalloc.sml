structure tigersimpleregalloc :> tigersimpleregalloc =
struct

  structure frame = tigerframe

  open tigerassem

	fun simpleregalloc (frm:frame.frame) (body:instr list) =
	let
		(* COMPLETAR: Temporarios que ya tienen color asignado (p.ej, el temporario que representa a rax) *)
		val precolored = tigerframe.allRegs
		(* COMPLETAR: Temporarios que se pueden usar (p.ej, el temporario que representa a rax. Diferencia con precolored: el temporario que representa a rbp no se puede usar) *)
		val asignables = ["r4","r5","r6","r7","r8","r9","r10"]

		fun intToString n = if n<0 then "-" ^ Int.toString(~n) else if n>=0 then Int.toString(n) else ""

		fun loadConstant n =
      let val const = intToString(n)
      in if n >= 0 andalso n <= tigerconstants.right16
         then "movw 'd0, #:lower16:" ^ const ^ "\n"
         else "movw 'd0, #:lower16:" ^ const ^ "\nmovt 'd0, #:upper16:" ^ const ^ "\n"
      end

		(* COMPLETAR: movaMem crea una instrucción que mueve un temporario a memoria. movaTemp, de memoria a un temporario.*)
		fun movaMem(temp, mempos, dirTemp) =
			OPER {assem= loadConstant(mempos) ^ "str 's0, [fp,'d0]\n", src=[temp], dst=[dirTemp], jump=NONE}
		fun movaTemp(mempos, temp, dirTemp) =
			OPER {assem= loadConstant(mempos) ^ "ldr 'd1, [fp,'d0]\n", src=[], dst=[dirTemp, temp], jump=NONE}
		
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
			| rewriteInstr (LABEL l) = [LABEL l] (*[LABEL {assem="hola\n", lab="hola"}]*)
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
