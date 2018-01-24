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

fun topsort p =
  let fun candidato p e =
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