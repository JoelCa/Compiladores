structure tigercodegen :> tigercodegen =
struct

structure A = tigerassem
structure T = tigertree
         
fun codegen (frame) (stm) =
  let val ilist = ref (nil : A.instr list)
      fun emit x = ilist := x :: !ilist
      fun result (gen) = let val t = tigertemp.newtemp() in gen t; t end
      fun munchStm (T.SEQ (a,b)) = (munchStm a; munchStm b)
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, e1, T.CONST i)), e2)) = emit (A.OPER { assem = "str 's0, ['s1,'s2]\n",
                                                                                           src = [munchExp e2, munchExp e1, munchExp (T.CONST i)],
                                                                                           dst = [],
                                                                                           jump = NONE } )
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, T.CONST i, e1)), e2)) = emit (A.OPER { assem = "str 's0, ['s1,'s2]\n",
                                                                                           src = [munchExp e2, munchExp e1, munchExp (T.CONST i)],
                                                                                           dst = [],
                                                                                           jump = NONE } )
        | munchStm (T.MOVE (T.MEM e1,T.MEM e2)) = emit ( A.OPER {assem = "str 's0, ['s1]\n",
                                                                 src = [munchExp (T.MEM e2), munchExp e1],
                                                                 dst = [],
                                                                 jump = NONE} )
        | munchStm (T.MOVE (T.MEM (T.CONST i), e2)) = emit (A.OPER { assem = "str 's0, ['s1]\n",
                                                                     src = [munchExp e2, munchExp (T.CONST i)],
                                                                     dst = [],
                                                                     jump = NONE })
        | munchStm (T.MOVE (T.MEM e1, e2)) = emit (A.OPER { assem = "str 's0, ['s1]\n",
                                                            src = [munchExp e2, munchExp e1],
                                                            dst = [],
                                                            jump = NONE })
        | munchStm (T.MOVE (T.TEMP i, e2)) = emit (A.OPER { assem = "mov 's0, 's1\n",
                                                            src = [munchExp (T.TEMP i), munchExp e2],
                                                            dst = [],
                                                            jump = NONE })
        (* | munchStm (T.SEQ(T.CJUMP (oper, e1, e2, t, f1), *)
        (*                   T.LABEL f2)) = let fun toAssemOper operacion =   (* CHEQUEAR: como se canoniza un CJUMP seguido de su label false y hacer comprobación de que f1 == f2 *) *)
        (*                                        case operacion of *)
        (*                                            EQ => "eq" *)
        (*                                          | NE => "ne" *)
        (*                                          | LT => "lt" *)
        (*                                          | GT => "gt" *)
        (*                                          | LE => "le" *)
        (*                                          | GE => "ge" *)
        (*                                          | ULT => "lo" *)
        (*                                          | ULE => "ls" *)
        (*                                          | UGT => "hi" *)
        (*                                          | UGE => "hs" *)
        (*                                  in emit (A.OPER { assem = "cmp s0 s1\n" ^ "b" ^ toAssemOper(oper) ^ t ^"\n", *)
        (*                                                    src = [munchExp e1, munchExp e2], *)
        (*                                                    dst = [], *)
        (*                                                    jump = SOME [t] }) *)
        (*                                  end *)
        | munchStm (T.JUMP (T.NAME s1, [s2])) = emit (A.OPER { assem = "b " ^ s1 ^ "\n", (* COMPARAR s1 y s2 *)
                                                               src = [],
                                                               dst = [],
                                                               jump = SOME [s1]})
        | munchStm (T.LABEL lab) =  emit (A.LABEL { assem = lab^":\n",
                                                    lab = lab} )
      and munchExp (T.MEM (T.BINOP (T.PLUS, e1, T.CONST i))) = result (fn r => emit (A.OPER { assem = "ldr 'd0, ['s0,'s1]\n",
                                                                                              src = [munchExp e1, munchExp (T.CONST i)],
                                                                                              dst = [r],
                                                                                              jump = NONE }))
        | munchExp (T.MEM (T.BINOP (T.PLUS, T.CONST i, e1))) = result (fn r => emit (A.OPER { assem = "ldr 'd0, ['s0,'s1]\n",
                                                                                              src = [munchExp e1, munchExp (T.CONST i)],
                                                                                              dst = [r],
                                                                                              jump = NONE }))
        | munchExp (T.MEM (T.CONST i)) = result (fn r => emit (A.OPER { assem = "ldr 'd0, ['s0]\n",
                                                                        src = [munchExp (T.CONST i)],
                                                                        dst = [r],
                                                                        jump = NONE }))
        | munchExp (T.MEM e1) = result (fn r => emit (A.OPER { assem = "ldr 'd0, ['s0]\n",
                                                               src = [munchExp e1],
                                                               dst = [r],
                                                               jump = NONE }))
        | munchExp (T.BINOP (T.PLUS, e1, T.CONST i)) = result (fn r => emit (A.OPER { assem = "add 'd0, 's0, 's1\n",
                                                                                      src = [munchExp e1, munchExp (T.CONST i)],
                                                                                      dst = [r],
                                                                                      jump = NONE }))
        | munchExp (T.BINOP (T.PLUS, T.CONST i, e1)) = result (fn r => emit (A.OPER { assem = "add 'd0, 's0, 's1\n",
                                                                                      src = [munchExp e1, munchExp (T.CONST i)],
                                                                                      dst = [r],
                                                                                      jump = NONE }))
        | munchExp (T.CONST i) = result (fn r => emit (A.OPER { assem = "ldr 'd0, =" ^ Int.toString(i) ^ "\n",
                                                                src = [],
                                                                dst = [r],
                                                                jump = NONE }))
        | munchExp (T.BINOP (T.PLUS, e1, e2)) = result (fn r => emit (A.OPER { assem = "add 'd0, 's0, 's1\n",
                                                                               src = [munchExp e1, munchExp e2],
                                                                               dst = [r],
                                                                               jump = NONE }))
        | munchExp (T.TEMP t) = t
  in munchStm stm;
     rev(!ilist)
  end

end
