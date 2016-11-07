structure Assem :
          sig
              type reg = string
              type temp = Temp.temp
              type label = Temp.label

              datatype instr = OPER of { assem : string ,
                                         dst : temp list,
                                         src : temp list,
                                         jump : label list option }
                             | LABEL of { assem : string,
                                          lab : Temp.label }
                             | MOVE of { assem : string ,
                                         dst : temp list,
                                         src : temp list }

              val format : (temp -> string) -> instr -> string

          end
