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

  fun replaceTemps _ _ [] = []
    | replaceTemps (src:string list) (dst:string list) (#"'"::(#"s"::(n::xs))) = 
        let
          val index = charToInt n
          val _ = print (Int.toString (length src))
          val temp = explode(List.nth(src, index))
          val _ = print (implode temp)
        in temp
        end
    | replaceTemps src dst (#"'"::(#"d"::(n::xs))) = 
        let
          val index = charToInt n
          val _ = print (Int.toString (length dst))
          val temp = explode(List.nth(dst, index))
          val _ = print (implode temp)
        in temp 
        end
    | replaceTemps src dst (other::xs) = 
      let val _ = print (implode [other])
      in other :: (replaceTemps src dst xs)
      end

  fun format (coloreo : temp -> string) (OPER {assem = s, dst = ds, src = ss, ...}) = implode (replaceTemps (map coloreo ds) (map coloreo ss) (explode s))
    | format _ (LABEL {assem = s, ...}) = s
    | format coloreo (MOVE {assem = s, dst = ds, src = ss}) = s
      (*let fun stringCompare (a : string) (b : string) =
            case String.compare(a,b) of
              EQUAL => true
            | _     => false
          val regSource = map coloreo ds
      in
        if List.all (stringCompare (List.hd(regSource))) (List.tl(regSource)) then ""
        else implode (replaceTemps regSource (map coloreo ss) (explode s))
      end*)
end