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

    fun format (_ : temp -> string) (OPER {assem = s, ...}) = s
      | format _ (LABEL {assem = s, ...}) = s
      | format _ _ = raise Fail "tigerassem: no debería pasar.\n"

end
