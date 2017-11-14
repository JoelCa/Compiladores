structure tigerconstants :> tigerconstants = struct

open Word

val right16 = 65535      (* 0000 0000 0000 0000 1111 1111 1111 1111 *)
val left16  = 4294901760 (* 1111 1111 1111 1111 0000 0000 0000 0000 *)

fun upper_lower(n:int) =
  let
    val w = fromInt n
    val lower = andb (w, (fromInt right16))
    val upper = >> (andb (w, (fromInt left16)), fromInt 16)
  in
    (toInt upper, toInt lower)
  end

end

(*
movw r0, #right
movt r0, #left
*)