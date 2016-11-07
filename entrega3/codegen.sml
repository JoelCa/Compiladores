fun codegen (frame) (stm : Tree.stm) : Assem.instr list =
  let val ilist = ref (nil : A.instr list)
      fun emit x = ilist := x::!ilist
      fun result (gen) = let val t = Temp.newtemp() in gen t; t end
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
                                                            src = [munchExp e2, munchExp e1],
                                                            dst = [],
                                                            jump = NONE })
        | munchStm (T.LABEL lab) =  emit (A.LABEL { assem = lab^":\n",
                                                    lab = lab} )
      and result (gen) = let val t = TEMP.newtemp() in gen t; t end
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
        | munchExp (T.CONST i) = result (fn r => emit (A.OPER { assem = "ldr 'd0, =" ^ int(i) ^ "\n",
                                                                src = [],
                                                                dst = [r],
                                                                jump = NONE }))
        | munchExp (T.BINOP (T.PLUS, e1, e2)) = result (fn r => emit (A.OPER { assem = "add 'd0, 's0, 's1\n",
                                                                               src = [munchExp e1, munchExp e2],
                                                                               dst = [r],
                                                                               jump = NONE }))
        | munchExp (T.TEMP t) = t
                                       
