structure tigerregalloc :> tigerregalloc =
struct
  open tigercolor
  open tigerframe
  open tigerassem

  structure Table = Splaymap
  

  val tempMap =
    foldr (fn (r, res) => insertAll (res, r, r)) emptyAll allRegs

  val accesses : (tigertemp.temp, int) Table.dict ref = ref (Table.mkDict String.compare)

  val stackInstrs : instr list ref = ref []

  fun intToString n = if n<0 then "-" ^ Int.toString(~n) else if n>=0 then Int.toString(n) else ""

  fun loadConstant n =
      let val const = intToString(n)
      in if n >= 0 andalso n <= tigerconstants.right16
         then "movw 'd0, #:lower16:" ^ const ^ "\n"
         else "movw 'd0, #:lower16:" ^ const ^ "\nmovt 'd0, #:upper16:" ^ const ^ "\n"
      end

    (* COMPLETAR: movaMem crea una instrucción que mueve un temporario a memoria. movaTemp, de memoria a un temporario.*)
    fun movaMem(temp, mempos) =
      let val dirTemp = tigertemp.newtemp()
      in OPER {assem = loadConstant(mempos) ^ "str 's0, [fp,'d0]\n", src=[temp], dst=[dirTemp], jump=NONE}
      end
    fun movaTemp(mempos, temp) =
      let val dirTemp = tigertemp.newtemp()
      in OPER {assem= loadConstant(mempos) ^ "ldr 'd1, [fp,'d0]\n", src=[], dst=[dirTemp, temp], jump=NONE}
      end
    

  fun makeStore(t:tigertemp.temp, f:frame):tigertemp.temp =
    let
      val t' = tigertemp.newtemp()
      val _ = case Table.peek (!accesses, t) of
                SOME n => stackInstrs := movaMem(t', n) :: !stackInstrs
              | NONE   => let val InFrame m = tigerframe.allocLocal f true
                              val _ = accesses := Table.insert (!accesses, t, m)
                          in
                            stackInstrs := movaMem(t', m) :: !stackInstrs
                          end
    in
      t'
    end

  fun makeLoad(t:tigertemp.temp, f:frame):tigertemp.temp =
    let
      val t' = tigertemp.newtemp()
      val _ = case Table.peek (!accesses, t) of
                SOME n => stackInstrs := movaTemp(n, t') :: !stackInstrs
              | NONE   => raise Fail "makeLoad: Quiere usar temporario que nunca definió."
    in
      t'
    end

  fun rewriteProgram([], frame, spilled) = 
      ([],frame)
    | rewriteProgram((OPER {assem = a, src = s, dst = d, jump = j})::instrs, frame, spilled) =
      let 
        val d' = map (fn t => if List.exists (fn x => x = t) spilled then makeStore (t,frame) else t) d
        val defInstrs = rev (!stackInstrs)
        val _ = stackInstrs := []
        val s' = map (fn t => if List.exists (fn x => x = t) spilled then makeLoad (t,frame) else t) s
        val useInstrs = rev (!stackInstrs)
        val _ = stackInstrs := []
        val instr' = OPER {assem = a, src = s', dst = d', jump = j}
        val (body',frame') = rewriteProgram(instrs, frame, spilled)
      in
        (useInstrs@[instr']@defInstrs@body', frame')
      end

    | rewriteProgram((MOVE {assem = a, src = s, dst = d})::instrs, frame, spilled) =
      let 
        val d' = map (fn t => if List.exists (fn x => x = t) spilled then makeStore (t,frame) else t) d
        val defInstrs = rev (!stackInstrs)
        val _ = stackInstrs := []
        val s' = map (fn t => if List.exists (fn x => x = t) spilled then makeLoad (t,frame) else t) s
        val useInstrs = rev (!stackInstrs)
        val _ = stackInstrs := []
        val instr' = MOVE {assem = a, src = s', dst = d'}
        val (body',frame') = rewriteProgram(instrs, frame, spilled)
      in
        (useInstrs@[instr']@defInstrs@body', frame')
      end
    | rewriteProgram(i::instrs, frame, spilled) =
      let val (body',frame') = rewriteProgram(instrs, frame, spilled)
      in (i::body', frame')
      end

  fun alloc(body, frame) =
    let val (color, spilled) = coloring({ code = body, initial = tempMap, spillCost = fn _ => 1, registers = allRegs })
        
    in 
      if spilled = []
      then (print "Fin del coloreo\n";
            (body, color))
      else
        let val (body', frame') = rewriteProgram(body,frame,spilled)
            val _ = print "Reescrituraaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa\n"
        in alloc(body', frame')
        end
    end
end