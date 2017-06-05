structure tigermg :> tigermg =
struct
  open tigergraph
  open tigerflow
  open tigerassem

  val instrNodes : instr table ref = ref (T.mkDict compareNodes)
  val labelProcesados : (string, node) T.dict ref = ref (T.mkDict String.compare)
  val jumpProcesados : (string, node list) T.dict ref = ref (T.mkDict String.compare)
  val labels : string list ref = ref []

  fun listToSet l = Splayset.addList (Splayset.empty String.compare, l)

  fun instr2graph [] = ({control = newGraph (), def = T.mkDict compareNodes, use = T.mkDict compareNodes, ismove = T.mkDict compareNodes},[])
    | instr2graph (x::instrs) =  
      let val (flowG, nodes) = instr2graph instrs
          val n = newNode (#control flowG)
          val _ = instrNodes := T.insert (!instrNodes, n, x)
          val _ = if null (!labels)
                  then ()
                  (* Al haber elementos en "labels" significa que la instr que estoy procesando es el posible destino de un jump *)
                  (* cuyo label este en "labels". *)
                  (* Para cada label en "labels", agregamos el nodo a labelProcesados, recorremos los jumpProcesados en busca de alguno *)
                  (* que lo tenga como destino y para los que coinciden, creamos la arista correspondiente. *)
                  else app (fn x => (T.insert (!labelProcesados, x, n);
                                          case T.peek (!jumpProcesados, x) of 
                                              SOME ns => app (fn n' => mk_edge (n', n)) ns
                                            | NONE    => () ))
                        (!labels)
          val is_jump = ref false
          val f = case x of
                      OPER {src = s, dst = d, jump = NONE, ...} =>
                        {control = #control flowG, def = T.insert (#def flowG, n, listToSet d), use = T.insert (#use flowG, n, listToSet s), ismove = T.insert (#ismove flowG, n, false)}
                    | OPER {src = s, dst = d, jump = SOME [j], ...} =>
                        let val _ = case T.peek (!labelProcesados, j) of
                                        SOME n' => mk_edge (n, n')
                                      | NONE    => case T.peek (!jumpProcesados, j) of
                                                  SOME w => jumpProcesados := T.insert (!jumpProcesados, j, n::w)
                                                | NONE   => jumpProcesados := T.insert (!jumpProcesados, j, [n])
                            val _ = if null s then is_jump := true else ()
                        in {control = #control flowG, def = T.insert (#def flowG, n, listToSet d), use = T.insert (#use flowG, n, listToSet s), ismove = T.insert (#ismove flowG, n, false)}
                        end
                    | LABEL {lab = l, ...} =>
                      let val _ = labels := l :: (!labels)
                      in flowG
                      end
                    | MOVE {src = s, dst = d, ...} =>
                      {control = #control flowG, def = T.insert (#def flowG, n, listToSet d), use = T.insert (#use flowG, n, listToSet s), ismove = T.insert (#ismove flowG, n, true)}
                    | _ => raise Fail "error: en instr2graph, no debería pasar."

          (* Si la instrucción es un jump común, entonces NO creamos una arista a la próxima instrucción. *)
          val _ = if null nodes orelse !is_jump then () else mk_edge (n, hd nodes)
      in
        (f, n::nodes)
      end
end