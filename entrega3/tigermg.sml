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

  fun addOptToList (SOME x) l = x::l 
    | addOptToList NONE l     = l

  fun instr2graph [] = ({control = newGraph (), def = T.mkDict compareNodes, use = T.mkDict compareNodes, ismove = T.mkDict compareNodes},[])
    | instr2graph (x::instrs) =  
      let val (flowG, nodes) = instr2graph instrs
          val optNode = case x of
                    LABEL _ => NONE
                  | _       => SOME (newNode (#control flowG))
          (* Al haber elementos en "labels" significa que la instr que estoy procesando es una instrucción siguiente a un label *)
          (* (que no es label) y es el posible destino de un jump cuyo label este en "labels". *)
          (* Para cada label en "labels", agregamos el nodo a labelProcesados, recorremos los jumpProcesados en busca de alguno *)
          (* que lo tenga como destino y para los que coinciden, creamos la arista correspondiente. *)
          val _ =
            case optNode of
              SOME n => 
                if null (!labels)
                  then ()
                  else (app (fn x => (T.insert (!labelProcesados, x, n);
                                      case T.peek (!jumpProcesados, x) of 
                                          SOME ns => app (fn n' => mk_edge (n', n)) ns
                                        | NONE    => () ))
                        (!labels) ; labels := [])
              | NONE => ()
          val is_jump = ref false
          (* A medida que se generan los nodos del grafo, se utilizan para armar el grafo de flujo (flowG) *)
          val f =
            case optNode of
              SOME n =>
                (case x of
                   OPER {src = s, dst = d, jump = NONE, ...} =>
                   ((*print "Procesando nodo en 1: "; printNode n; print "\n"; *){control = #control flowG, def = T.insert (#def flowG, n, listToSet d), use = T.insert (#use flowG, n, listToSet s), ismove = T.insert (#ismove flowG, n, false)})
                 | OPER {src = s, dst = d, jump = SOME [j], ...} =>
                   let val _ = case T.peek (!labelProcesados, j) of
                                   SOME n' => mk_edge (n, n')
                                 | NONE    => case T.peek (!jumpProcesados, j) of
                                             SOME w => jumpProcesados := T.insert (!jumpProcesados, j, n::w)
                                           | NONE   => jumpProcesados := T.insert (!jumpProcesados, j, [n])
                       val _ = if null s then is_jump := true else ()
                   in ((*print "Procesando nodo en 2: "; printNode n; print "\n";*) {control = #control flowG, def = T.insert (#def flowG, n, listToSet d), use = T.insert (#use flowG, n, listToSet s), ismove = T.insert (#ismove flowG, n, false)})
                   end
                 | MOVE {src = s, dst = d, ...} =>
                   {control = #control flowG, def = T.insert (#def flowG, n, listToSet d), use = T.insert (#use flowG, n, listToSet s), ismove = T.insert (#ismove flowG, n, true)}
                 | _ => raise Fail "error: en instr2graph, no debería pasar.")
              | NONE => 
                case x of
                  LABEL {lab = l, ...} =>
                    let val _ = labels := l :: (!labels)
                    in flowG
                    end
                | _ => raise Fail "error: en instr2graph, no debería pasar 2."
          (* Si la instrucción es un jump común, entonces NO creamos una arista a la próxima instrucción. *)
          val _ =
            case optNode of
              SOME n => if null nodes orelse !is_jump then () else mk_edge (n, hd nodes)
            | NONE   => ()
      in
        (f, addOptToList optNode nodes)
      end
end

(*
                        jump L2
                        .
                        .
                        .
                        jump L2
                        .
                        .
                        .
                        label L2
                        mov r1, r2 <--- nodo n
                        .
                        .
                        .
                        jump L2
                        .
                        .
                        .
                        jump L3
                        .
                        .
                        .
                        jump L3
                        .
                        .
                        .
                        label L3
                        str ..
*)
