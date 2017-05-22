structure tigermg :> tigermg =
struct
  open tigergraph
  open tigerflow
  open tigerassem

  val instrNodes : instr table ref = ref (T.mkDict compareNodes)
  val labelProcesados : (string, node) T.dict ref = ref (T.mkDict String.compare)
  val jumpProcesados : (string, node list) T.dict ref = ref (T.mkDict String.compare)

  fun instr2graph [] = ({control = newGraph (), def = T.mkDict compareNodes, use = T.mkDict compareNodes, ismove = T.mkDict compareNodes},[])
    | instr2graph (x::instrs) =  
      let val (flowG, nodes) = instr2graph instrs
          val n = newNode (#control flowG)
          val _ = instrNodes := T.insert (!instrNodes, n, x)
          val _ = if null nodes then () else mk_edge (n, hd nodes)
          val f = case x of
                      OPER {src = s, dst = d, jump = NONE, ...} =>
                        {control = #control flowG, def = T.insert (#def flowG, n, d), use = T.insert (#use flowG, n, s), ismove = T.insert (#ismove flowG, n, false)}
                    | OPER {src = s, dst = d, jump = SOME [j], ...} =>
                        let val _ = case T.peek (!labelProcesados, j) of
                                        SOME n' => mk_edge (n, n')
                                      | NONE => let val _ = case T.peek (!jumpProcesados, j)of
                                                                SOME w => jumpProcesados := T.insert (!jumpProcesados, j, n::w)
                                                              | NONE => jumpProcesados := T.insert (!jumpProcesados, j, [n])
                                                in () end
                        in {control = #control flowG, def = T.insert (#def flowG, n, d), use = T.insert (#use flowG, n, s), ismove = T.insert (#ismove flowG, n, false)}
                        end
                      | LABEL {lab = l, ...} =>
                        let val _ = case T.peek (!jumpProcesados, l) of
                                        SOME ns => foldl (fn (x, _) => mk_edge (x, n)) () ns
                                      | NONE => ()
                            val _ = labelProcesados := T.insert (!labelProcesados, l, n)
                        in {control = #control flowG, def = T.insert (#def flowG, n, []), use = T.insert (#use flowG, n, []), ismove = T.insert (#ismove flowG, n, false)}                      
                        end
                      | MOVE {src = s, dst = d, ...} =>
                        {control = #control flowG, def = T.insert (#def flowG, n, d), use = T.insert (#use flowG, n, s), ismove = T.insert (#ismove flowG, n, true)}
                      | _ => raise Fail "error: en instr2graph, no debería pasar."
      in
        (f, n::nodes)
      end
end