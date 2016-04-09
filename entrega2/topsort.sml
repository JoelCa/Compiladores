(*Operaciones básicas copiadas de la carpeta*)

infix -- ---
infix rs ls

fun x ls f = fn y => f(x,y)
fun f rs y = fn x => f(x,y)
fun l -- e = List.filter (op <> rs e) l
fun fst (x, _) = x and snd (_, y) = y
fun lp --- e = List.filter ((op <> rs e) o fst) lp

open tigerabs

exception Ciclo


local (* Sort topolo'gico *)
	fun cmp(x, y) = x=y
	fun mem(x, []) = false
	| mem(x, y::l) = cmp(x, y) orelse mem(x, l)
	fun nexts(a, []) = []
	| nexts(a, (x, y)::pairs) =
		if cmp(a, x) then y::nexts(a, pairs) else nexts(a, pairs)
in
	fun topsort graph =
		let	fun sort([], path, visited) = visited
			| sort(x::xs, path, visited) =
				if mem(x, path) then raise Fail "ciclo!"
				else sort(xs, path,
						if mem(x, visited) then visited
						else x::sort(nexts(x, graph), x::path, visited))
			val (starts, _) = ListPair.unzip graph
		in	sort(starts, [], []) end
end
(*
(* 3 *)
(* a esto hay que mejorarlo mucho! *)
fun integraTEnvs(env, env') =
	let	val res = fromTab env
		fun aux(c, v) = tabRInserta(c, v, res)
	in
		tabAplica(aux, env');
		res
	end
(*------------------------------*)

fun muestra(s, t)=
	let	fun aux(NameTy t) = print("NameTy "^t)
		| aux(ArrayTy t) = print("ArrayTy "^t)
		| aux(RecordTy l) =
			let	fun f{name, typ,...} =
					(print(name^" "); aux typ)
			in
				(print "RecordTy "; app f l)
			end
	in
		print s; print "    "; aux t; print "\n"
	end
fun string2Ty(s, t) = (NameTy s, t)
val t = colectaNameTy prueba
val l = List.map string2Ty (tabAList t);
val r = topsort l;
*)

(*Código copiado de la carpeta*)
fun topsort p =
    let
        fun candidato p e =
            List.filter (fn e => List.all ((op <> rs e) o  snd) p) e
        fun tsort p [] res = rev res
          | tsort [] st res = rev (st @ res)
          | tsort p (st as (h :: t)) res =
            let val x = (hd (candidato p st))
                        handle Empty => raise Ciclo
            in tsort (p --- x) (st -- x) (x :: res) end
        fun elementos lt =
            List.foldl (fn ((x,y),l) =>
                             let val l1 = case List.find (op = rs x) l of
                                              NONE => x :: l | _ => l
                                 val l2 = case List.find (op = rs y) l1 of
                                              NONE => y :: l1 | _ => l1
                             in l2 end) [] lt
    in tsort p (elementos p) []
    end
