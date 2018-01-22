structure tigerregalloc :> tigerregalloc =
struct
  open tigercolor
  open tigerframe
  open tigerassem

  structure Table = Splaymap
  structure Set = Splayset

  val tempMap =
    foldr (fn (r, res) => insertAll (res, r, r)) emptyAll allRegs

  val accesses : (tigertemp.temp, int) Table.dict ref = ref (Table.mkDict String.compare)

  val stackInstrs : instr list ref = ref []

  val newTemps : tigertemp.temp Set.set ref = ref (Set.empty String.compare)

  val spillHeuristic : (tigertemp.temp, int) Table.dict ref = ref (Table.mkDict String.compare)

  fun intToString n = if n<0 then "-" ^ Int.toString(~n) else if n>=0 then Int.toString(n) else ""

  fun loadConstant n =
    let val const = intToString(n)
    in if n >= 0 andalso n <= tigerconstants.right16
       then "movw 'd0, #:lower16:" ^ const ^ "\n"
       else "movw 'd0, #:lower16:" ^ const ^ "\nmovt 'd0, #:upper16:" ^ const ^ "\n"
    end

  fun movaMem(temp, mempos) =
    let val dirTemp = tigertemp.newtemp()
        val _ = newTemps := Set.add (!newTemps, dirTemp)
    in (OPER { assem = "str 's0, [fp,'s1]\n", 
               src=[temp, dirTemp], 
               dst=[], 
               jump=NONE}) ::
       [OPER { assem = loadConstant(mempos),
               src = [],
               dst = [dirTemp],
               jump = NONE }]
    end
  fun movaTemp(mempos, temp) =
    let val dirTemp = tigertemp.newtemp()
        val _ = newTemps := Set.add (!newTemps, dirTemp)
    in (OPER { assem = "ldr 'd0, [fp,'s0]\n", 
               src = [dirTemp], 
               dst = [temp], 
               jump=NONE}) ::
       [OPER { assem = loadConstant(mempos),
               src = [],
               dst = [dirTemp],
               jump = NONE }]
    end
    

  fun makeStore(t:tigertemp.temp, f:frame):tigertemp.temp =
    let
      val t' = tigertemp.newtemp()
      val _ = case Table.peek (!accesses, t) of
                SOME n => stackInstrs := movaMem(t', n) @ !stackInstrs
              | NONE   => let val InFrame m = tigerframe.allocLocal f true
                              val _ = accesses := Table.insert (!accesses, t, m)
                          in
                            stackInstrs := movaMem(t', m) @ !stackInstrs
                          end
    in
      t'
    end

  fun makeLoad(t:tigertemp.temp, f:frame):tigertemp.temp =
    let
      val t' = tigertemp.newtemp()
      val _ = case Table.peek (!accesses, t) of
                SOME n => stackInstrs := movaTemp(n, t')  @ !stackInstrs
              | NONE   => raise Fail "makeLoad: Quiere usar temporario que nunca definió."
    in
      t'
    end

  fun rewriteProgram([], frame, spilled) =
      ([],frame)
    | rewriteProgram((OPER {assem = a, src = s, dst = d, jump = j})::instrs, frame, spilled) =
      let val d' = map (fn t => if List.exists (fn x => x = t) spilled
                                then let val tt = makeStore (t,frame) in newTemps := Set.add (!newTemps, tt); tt end
                                else t) d
          val defInstrs = rev (!stackInstrs)
          val _ = stackInstrs := []
          val s' = map (fn t => if List.exists (fn x => x = t) spilled
                                then let val tt = makeLoad (t,frame)
                                     in newTemps := Set.add (!newTemps, tt); tt end
                                else t) s
          val useInstrs = rev (!stackInstrs)
          val _ = stackInstrs := []
          val instr' = OPER {assem = a, src = s', dst = d', jump = j}
          val (body',frame') = rewriteProgram(instrs, frame, spilled)
      in
        (useInstrs@[instr']@defInstrs@body', frame')
      end

    | rewriteProgram((MOVE {assem = a, src = s, dst = d})::instrs, frame, spilled) =
      let val d' = map (fn t => if List.exists (fn x => x = t) spilled
                                then let val tt = makeStore (t,frame) in newTemps := Set.add (!newTemps, tt); tt end
                                else t) d
          val defInstrs = rev (!stackInstrs)
          val _ = stackInstrs := []
          val s' = map (fn t => if List.exists (fn x => x = t) spilled
                                then let val tt = makeLoad (t,frame)
                                     in newTemps := Set.add (!newTemps, tt); tt end
                                else t) s
          val useInstrs = rev (!stackInstrs)
          val _ = stackInstrs := []
          val instr' = MOVE {assem = a, src = s', dst = d'}
          val (body',frame') = rewriteProgram(instrs, frame, spilled)
      in
        (useInstrs@(instr'::(defInstrs@body')), frame')
      end
    | rewriteProgram(i::instrs, frame, spilled) =
      let val (body',frame') = rewriteProgram(instrs, frame, spilled)
      in
        (i::body', frame')
      end

  fun increaseSpillCost(t : tigertemp.temp) = 
    case Table.peek(!spillHeuristic, t) of
      SOME n => spillHeuristic := Table.insert(!spillHeuristic,t,n+1)
    | NONE   => spillHeuristic := Table.insert(!spillHeuristic,t,1)

  fun buildHeuristic [] = ()
    | buildHeuristic ((OPER {src = s, dst = d, ...})::instrs) =
      (List.app increaseSpillCost s;
       List.app increaseSpillCost d;
       buildHeuristic instrs)
    | buildHeuristic ((MOVE {src = s, dst = d, ...})::instrs) = 
      (List.app increaseSpillCost s;
       List.app increaseSpillCost d;
       buildHeuristic instrs)
    | buildHeuristic (_::instrs) = buildHeuristic instrs


  fun alloc(body, frame) =
    let val _ = buildHeuristic(body)
        val (color, spilled) = coloring({ code = body, initial = tempMap, spillCost = spillHeuristic, registers = allRegs })
        val _ = spillHeuristic := Table.mkDict String.compare
    in 
      if spilled = []
      then (initializeColoring(!newTemps);
            accesses := Table.mkDict String.compare;
            newTemps := Set.empty String.compare;    
            (body, color))
      else 
        let val (body', frame') = rewriteProgram(body,frame,spilled)
            val _ = initializeColoring(!newTemps)
            val _ = accesses := Table.mkDict String.compare
            val _ = newTemps := Set.empty String.compare
        in alloc(body', frame')
        end
    end

end