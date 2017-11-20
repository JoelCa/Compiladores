structure tigerassem =
struct
  type reg = string
  type temp = tigertemp.temp
  type label = tigertemp.label

  datatype instr = OPER of { assem : string ,
                             dst : temp list,
                             src : temp list,
                             jump : label list option }
                 | LABEL of { assem : string,
                              lab : label }
                 | MOVE of { assem : string ,
                             dst : temp list,
                             src : temp list }

  fun charToInt c = 
    if ord(c) > 47 andalso ord(c) < 58 then
      ord(c) - 48
    else
      raise Fail "No debería pasar! (charToInt)"

  fun printInstr (OPER {assem = a, dst = d, src = s, ...}) =
        let val _ = print ("OPER\n")
            val _ = print (a^"\n")
            val _ = print ("DST: ")
            val _ = List.app (fn e => print (e^" ")) d
            val _ = print "\n"
            val _ = print ("SRC: ")
            val _ = List.app (fn e => print (e^" ")) s
            val _ = print "\n-------------------\n\n"
        in () end
    | printInstr (MOVE {assem = a, dst = d, src = s}) =
        let val _ = print ("MOVE\n")
            val _ = print (a^"\n")
            val _ = print ("DST: ")
            val _ = List.app (fn e => print (e^" ")) d
            val _ = print "\n"
            val _ = print ("SRC: ")
            val _ = List.app (fn e => print (e^" ")) s
            val _ = print "\n-------------------\n\n"
        in () end
    | printInstr (LABEL {assem = a, ...}) =
        print ("LABEL\n"^a^"\n-------------------\n\n")
        


  fun replaceTemps _ _ [] = []
    | replaceTemps (src:string list) (dst:string list) (#"'"::(#"s"::(n::xs))) = 
        let
          val index = charToInt n
          (*val _ = print ((Int.toString (length src))^"  --------    "^(Int.toString index)^"\n")*)
          val temp = explode(List.nth(src, index))
        in temp @ replaceTemps src dst xs
        end
    | replaceTemps src dst (#"'"::(#"d"::(n::xs))) = 
        let
          val index = charToInt n
          (*val _ = print ((Int.toString (length dst))^" "^(Int.toString index)^"\n")*)
          val temp = explode(List.nth(dst, index))
        in temp @ replaceTemps src dst xs
        end
    | replaceTemps src dst (other::xs) = other :: (replaceTemps src dst xs)      

  fun format (coloreo : temp -> string) (OPER {assem = s, dst = dst, src = src, ...}) = 
        implode (replaceTemps (map coloreo src) (map coloreo dst) (explode s))
    | format _ (LABEL {assem = s, ...}) = s
    | format coloreo (MOVE {assem = s, dst = dst, src = src}) = implode (replaceTemps (map coloreo src) (map coloreo dst) (explode s))
(*      let val regSource = map coloreo src
          val regDestination = map coloreo dst
      in
        if regSource = regDestination then ""
        else implode (replaceTemps regSource (map coloreo dst) (explode s))
      end*)
end