structure tigercodegen :> tigercodegen =
struct

structure A = tigerassem
structure T = tigertree

open tigerframe
open tigerconstants

(* T.MOVE (a, b)  <-----> a := b *)

fun codegen (frame) (stm) =
  let val ilist = ref (nil : A.instr list)
      fun emit x = ilist := x :: !ilist
      fun result (gen) = let val t = tigertemp.newtemp() in gen t; t end
      fun intToString n = if n<0 then "-" ^ Int.toString(~n) else if n>=0 then Int.toString(n) else ""
      fun munchStm (T.SEQ (a,b)) = (munchStm a; munchStm b)
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, e1, T.CONST i)), e2)) = emit (A.OPER { assem = "str 's0, ['s1,'s2]\n",
                                                                                           src = [munchExp e2, munchExp e1, munchExp (T.CONST i)],
                                                                                           dst = [],
                                                                                           jump = NONE } )
        | munchStm (T.MOVE (T.MEM (T.BINOP (T.PLUS, T.CONST i, e1)), e2)) = emit (A.OPER { assem = "str 's0, ['s1,'s2]\n",
                                                                                           src = [munchExp e2, munchExp e1, munchExp (T.CONST i)],
                                                                                           dst = [],
                                                                                           jump = NONE } )
        (* Este caso esta MAL. NO guarda en la posición de memoria e1 la etiqueta l.
        | munchStm (T.MOVE (T.MEM e1, T.NAME l)) = emit (A.OPER { assem = "ldr 's0, =" ^ l ^ "\n",
                                                                  src = [munchExp e1],
                                                                  dst = [],
                                                                  jump = NONE })  *)        
        | munchStm (T.MOVE (T.MEM e1, e2)) = emit (A.OPER { assem = "str 's0, ['s1]\n",
                                                            src = [munchExp e2, munchExp e1],
                                                            dst = [],
                                                            jump = NONE })
        | munchStm (T.MOVE (T.TEMP i, e2)) = emit (A.MOVE { assem = "mov 'd0, 's0\n",
                                                            src = [munchExp e2],
                                                            dst = [i] })

        | munchStm (T.CJUMP (oper, e1, e2, t, _)) = let fun toAssemOper operacion = 
                                                          case operacion of
                                                              T.EQ  => "eq"
                                                            | T.NE  => "ne"
                                                            | T.LT  => "lt"
                                                            | T.GT  => "gt"
                                                            | T.LE  => "le"
                                                            | T.GE  => "ge"
                                                            | T.ULT => "lo"
                                                            | T.ULE => "ls"
                                                            | T.UGT => "hi"
                                                            | T.UGE => "hs"
                                                    in emit (A.OPER { assem = "cmp 's0, 's1\n" ^ "b" ^ toAssemOper(oper) ^ " " ^ t ^"\n",
                                                                      src = [munchExp e1, munchExp e2],
                                                                      dst = [],
                                                                      jump = SOME [t] })
                                                    end
        | munchStm (T.JUMP (T.NAME s, _)) = emit (A.OPER { assem = "b " ^ s ^ "\n",
                                                           src = [],
                                                           dst = [],
                                                           jump = SOME [s]})
        | munchStm (T.LABEL lab) =  emit (A.LABEL { assem = lab^":\n", lab = lab} )
        | munchStm (T.EXP (T.CALL (T.NAME name,args))) =  let val (rList, mList) = munchArgs (0,args)
                                                          in emit (A.OPER { assem = "bl " ^ name ^ "\n",
                                                                            src = rList,
                                                                            dst = calldefs,
                                                                            jump = SOME [name]}) 
                                                            ; makePops mList
                                                          end
        | munchStm (T.EXP e) = emit (A.OPER { assem = "",
                                              src = [munchExp e],
                                              dst = [],
                                              jump = NONE})
        | munchStm _ = raise Fail "No debería llegar! (munchStm)"

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
        | munchExp (T.BINOP (T.DIV, e1, e2)) = munchExp (T.CALL (T.NAME "divide", [e1,e2]))
        | munchExp (T.BINOP (oper, e1, e2)) = let fun toAssemOper operation =
                                                    case operation of
                                                        T.PLUS  => "add"
                                                      | T.MINUS => "sub"
                                                      | T.MUL   => "mul"
                                                      | T.DIV   => raise Fail "No debería pasar! (munchExp2)\n"
                                                      | T.AND   => "and"
                                                      | T.OR    => "orr"
                                                      | T.XOR   => "eor"
                                                      | _       => raise Fail "No debería pasar! (munchExp1)\n"
                                                  fun assemCode operation = 
                                                    case operation of
                                                        T.LSHIFT   => "mov 'd0, 's0, lsl 's1\n"
                                                      | T.RSHIFT   => "mov 'd0, 's0, lsr 's1\n"
                                                      | T.ARSHIFT  => "mov 'd0, 's0, asr 's1\n"
                                                      | oper  => toAssemOper(oper) ^ " 'd0, 's0, 's1\n"
                                              in result (fn r => emit (A.OPER { assem = assemCode oper,
                                                                                src = [munchExp e1, munchExp e2],
                                                                                dst = [r],
                                                                                jump = NONE }))
                                              end
        | munchExp (T.CALL f) = result (fn r => munchStm (T.SEQ (T.EXP (T.CALL f), T.MOVE (T.TEMP r, T.TEMP rv))))
        | munchExp (T.CONST i) = let fun checkInt n =
                                       if n <= right16
                                       then "movw 'd0, #" ^ intToString(n)
                                 in result (fn r => emit (A.OPER { assem = "ldr 'd0, = " ^ intToString(i) ^ "\n",
                                                                src = [],
                                                                dst = [r],
                                                                jump = NONE }))
        | munchExp (T.NAME l) = result (fn r => emit (A.OPER { assem = "ldr 'd0, =" ^ l ^ "\n",
                                                               src = [],
                                                               dst = [r],
                                                               jump = NONE }))
        | munchExp (T.TEMP t) = t
        | munchExp e = let val _ = print (tigerit.tree (T.EXP e))
                       in raise Fail "No debería llegar! (munchExp2)"
                       end

      and munchArgs (_,[])     = ([], [])
        | munchArgs (n, x::xs) = if n < 4 then let val y = List.nth (tigerframe.argregs, n)
                                                   val _ = munchStm (T.MOVE (T.TEMP y, x))
                                                   val (r1,r2) = munchArgs (n+1, xs)
                                               in (y :: r1, r2)
                                               end
                                 else let val z = munchExp x
                                          val _ = emit (A.OPER { assem = "push {'s0}\n",
                                                                 src = [z],
                                                                 dst = [],
                                                                 jump = NONE } )
                                          val (r1, r2) = munchArgs (n+1, xs)
                                      in (r1, z :: r2)
                                      end
      and makePops []      = ()
        | makePops (x::xs) =  let val _ = emit (A.OPER { assem = "pop {'s0}\n",
                                                         src = [x],
                                                         dst = [],
                                                         jump = NONE } )
                              in makePops xs
                              end
  in munchStm stm;
     rev(!ilist)
  end


fun maximalMunch f [] = []
  (*| maximalMunch f ((h as T.CJUMP _)::_::t) = codegen f h @ maximalMunch f t *)
  (* El caso comentado esta mal, pues NO podemos ignorar el segundo elemento de la lista, más alla de que éste sea siempre el label false del CJUMP *)
  | maximalMunch f (h::t) = codegen f h @ maximalMunch f t
      
end
