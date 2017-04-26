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
          val temp = explode(List.nth(src, index))
        in temp @ replaceTemps src dst xs
        end
    | replaceTemps src dst (#"'"::(#"d"::(n::xs))) = 
        let
          val index = charToInt n
          val temp = explode(List.nth(dst, index))
        in temp @ replaceTemps src dst xs
        end
    | replaceTemps src dst (other::xs) = other :: (replaceTemps src dst xs)      

  fun format (coloreo : temp -> string) (OPER {assem = s, dst = dst, src = src, ...}) = implode (replaceTemps (map coloreo src) (map coloreo dst) (explode s))
    | format _ (LABEL {assem = s, ...}) = s
    | format coloreo (MOVE {assem = s, dst = dst, src = src}) =
      let fun stringCompare (a : string) (b : string) =
            case String.compare(a,b) of
              EQUAL => true
            | _     => false
          val regSource = map coloreo src
      in
        if List.all (stringCompare (List.hd(regSource))) (List.tl(regSource)) then ""
        else implode (replaceTemps regSource (map coloreo dst) (explode s))
      end
end