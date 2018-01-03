structure tigercolor :> tigercolor = 
struct
  
  open tigerassem
  open tigergraph
  open tigerliveness

  structure Table = Splaymap
  structure Set = Splayset
  
  type allocation = (tigertemp.temp, tigerframe.register) Table.dict

  val emptyAll = Table.mkDict String.compare
  fun insertAll x = Table.insert x
  fun findAll x = Table.find x
  fun printAll t = Table.app (fn (k,x) => ((print "coloreo final"); (print ("("^k^","^x^")")); (print "\n"))) t


  fun adjSetCompare((a,b),(c,d)) = case tigertemp.compare(a,c) of
                                     EQUAL => tigertemp.compare(b,d)
                                   | other => other

  val moveList : (tigertemp.temp, tigergraph.node Set.set) Table.dict ref = ref (Table.mkDict String.compare)
  val worklistMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  (*val adjSet : (tigertemp.temp * tigertemp.temp) Set.set ref =
    ref (Set.empty (fn (x,y) => if funAux(x,y) then EQUAL else LESS))*)
  val adjSet : (tigertemp.temp * tigertemp.temp) Set.set ref =
    ref (Set.empty adjSetCompare)
  val adjList : (tigertemp.temp, tigertemp.temp Set.set) Table.dict ref = ref (Table.mkDict String.compare)
  val degree : (tigertemp.temp, int) Table.dict ref = ref (Table.mkDict String.compare)
  val precolored : tigerframe.register Set.set = Set.addList((Set.empty String.compare), tigerframe.allRegs)
  val initial : tigertemp.temp Set.set ref = ref  (Set.empty String.compare)
  val spillWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
  val colorCount = (length tigerframe.allRegs) - 5
  val activeMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val freezeWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
  val simplifyWorklist : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
  val selectStack : tigertemp.temp list ref = ref []
  val coalescedNodes : tigertemp.temp Set.set ref = ref (Set.empty String.compare)
  val movesPair : (tigergraph.node, tigertemp.temp * tigertemp.temp) Table.dict ref = ref (Table.mkDict tigergraph.compareNodes)
  val coalescedMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val constrainedMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val alias : (tigertemp.temp, tigertemp.temp) Table.dict ref = ref (Table.mkDict String.compare)
  val frozenMoves : tigergraph.node Set.set ref = ref (Set.empty compareNodes)
  val coloredNodes : tigerframe.register Set.set ref = ref (Set.empty String.compare)
  val color : (tigertemp.temp, int) Table.dict ref = 
    ref (Table.mkDict String.compare) (*(#1 (List.foldl (fn (r, (res,n)) => (Table.insert (res, r, n),n+1)) (Table.mkDict String.compare, 0) tigerframe.allRegs))*)
  val spilledNodes : tigertemp.temp Set.set ref = ref (Set.empty String.compare)  
  val colores = [("r0",0),("r1",1),("r2",2),("r3",3),("r4",4),("r5",5), 
                 ("r6",6),  ("r7",7), ("r8",8),("r9",9),("r10",10),
                 ("fp",11),("ip",12),("sp",13),("lr",14),("pc",15)]


  fun initialColor() =
    let val _ = color := Table.mkDict String.compare
    in List.app (fn (x,y) => color := Table.insert (!color, x, y)) colores
    end

      
  (* ####################### Table and set functions ####################### *)

  fun peekTableValue(t,x) = Table.peek(!t, x)
  
  fun getTableValue(t,x) = Table.find(!t, x)
  
  fun updateTable(t,n,f) =
    t := Table.insert(!t, n, f (peekTableValue(t, n)))

  fun updateSetTable(t,n,x) =
    updateTable(t,n, fn opt => 
                       case opt of
                         SOME y => Set.union(y, x)
                       | NONE   => x) 
    
  fun updateSet(s,x) =
    s := Set.add(!s, x)

  fun removeElemTempSet(s,x) =
    s := Set.difference(!s, Set.singleton String.compare x)

  fun removeElemNodeSet(s,x) =
    s := Set.difference(!s, Set.singleton tigergraph.compareNodes x)

  fun removeElemIntSet(s,x) =
    s := Set.difference(!s, Set.singleton Int.compare x)

  fun listToSet(l) =
    Set.addList(Set.empty String.compare, !l)

  fun push(x,xs) = xs := x::(!xs)
  
  (*FALTA TRATAR EL TEMA DE CUANDO XS ES VACIO*)
  fun pop (ref []) = raise Fail "Error Pop lista vacia\n"
    | pop xs = 
        let val x = hd(!xs)
        in (xs := tl(!xs); x)
        end

  fun inSet(x,s) = Set.member(!s, x)

  fun inSetNoRef(x,s) = Set.member(s, x)

  fun takeElem(s) = Set.find (fn _ => true) (!s)

  fun singleTempSet(x) = Set.singleton String.compare x

  fun singleNodeSet(x) = Set.singleton tigergraph.compareNodes x

  fun getDegree(x) =
    case peekTableValue(degree,x) of
      SOME d => d
    | NONE   => 0

  (* ####################################################################### *)


  fun addEdge (u,v) =
    let
      (*val _ = (print ("\n"^Bool.toString(inSet((u,v), adjSet))^u^","^v^"   <----->   "^Bool.toString(inSetNoRef(u, precolored))^","^Bool.toString(inSetNoRef(v, precolored))); print "\n")
      val _ = print "Conjunto de adjacencia\n"
      val _ = Set.app (fn (x,y) => print (x ^ "," ^ y ^ " - ")) (!adjSet)*)
    in
      if not(inSet((u,v), adjSet)) andalso not(u = v)
      then
        let val _ = adjSet := Set.add (Set.add (!adjSet, (u,v)), (v,u))
            val _ = if not(inSetNoRef(u, precolored))
                    then (updateSetTable(adjList,u, singleTempSet(v));                      
                          updateTable (degree, u, fn opt =>
                                                    case opt of
                                                      SOME x => x+1
                                                    | NONE   => 1);
                          updateSet(initial, u))
                    else ()
            val _ = if not(inSetNoRef(v, precolored))
                    then (updateSetTable(adjList,v, singleTempSet u);
                          updateTable (degree, v, fn opt =>
                                                    case opt of
                                                      SOME x => x+1
                                                    | NONE   => 1);
                          updateSet(initial, v))
                    else ()
        in () end
      else ()
    end


  fun livenessAnalysis (body : instr list) = 
    let val _   = tigermg.initialize()
        val res = #1 (tigermg.instr2graph body)
    in res end


  fun build (flowg : tigerflow.flowgraph) =
    let val g      = #control flowg
        val moves  = #ismove flowg
        val instrs = tigergraph.nodes g
        val _      = tigerliveness.initialize()
        val louts  = tigerliveness.liveOuts flowg
        (*type liveSet = tigertemp.temp Splayset.set
        type liveMap = liveSet tigergraph.table

        val liveOuts : tigerflow.flowgraph -> liveMap*)
        val _ = T.app (fn (n,live_outs) => (print "\n----- "; printNode n; print " -----\n"; Set.app (fn t => print (t^"  ")) live_outs; print "\n---------------\n")) louts
        fun buildAux i = 
          let val live = ref (T.find (louts, i))
              val useSet = T.find (#use flowg, i)
              val defSet = T.find (#def flowg, i)
              val _ = if T.find (moves, i)
                      then
                        let
                          (*val _ = live := Set.difference (!live, useSet)*)
                          val _ = Set.app (fn d => Set.app (fn u => movesPair := Table.insert(!movesPair, i, (d,u))) useSet) defSet
                        in
                          Set.app (fn x => updateSetTable(moveList, x, singleNodeSet(i))) (Set.union (defSet,useSet));
                          updateSet(worklistMoves, i)
                        end
                      else
                        ()
              val _ = print "\n------------"
              val _ = (print ("\ndefSet "); printNode i; print "\n")
              val _ = Set.app (fn x => print (x ^ " - ")) defSet
              val _ = (print ("\nlive outs "); printNode i; print "\n")
              val _ = Set.app (fn y => print (y ^ " - ")) (!live)
              val _ = live := Set.union (!live, defSet)
              val _ = (print ("\nlive outs unidos con defs "); printNode i; print "\n")
              val _ = Set.app (fn y => print (y ^ " - ")) (!live)
              val _ = print "\n"
          in
            Set.app (fn a =>
                      Set.app (fn b => (addEdge (a,b); print ("Se creó la arista: " ^ a ^ " <---> " ^ b ^ "\n"))) (!live)
                    ) defSet
          end
    in
      app buildAux instrs
    end

  fun nodeMoves(n) =
    case peekTableValue(moveList, n) of
      SOME ms => Set.intersection(ms, Set.union(!activeMoves, !worklistMoves))
    | NONE    => Set.empty compareNodes
  
  fun moveRelated(n) =
    not(Set.isEmpty(nodeMoves(n)))

  fun makeWorkList () =
    let
      (*val _ = Table.app (fn (k,x) => ((print "lista de nodos"); (print ("("^k^","^Int.toString x^")")); (print "\n"))) (!degree)
      val _ = Set.app (fn k => ((print "nodos precolorados"); (print ("("^k^")")); (print "\n"))) (precolored)*)
      fun makeWorkL x =
        let
          val _ = removeElemTempSet(initial, x)
        in
          if getDegree(x) >= colorCount
          then
            updateSet(spillWorklist, x)
          else 
            if moveRelated(x)
            then updateSet(freezeWorklist, x)
            else ((*print ("Se agrega en 1: " ^ x ^ "\n");*) updateSet(simplifyWorklist, x))
        end
    in
      Set.app makeWorkL (!initial)
    end

  fun adjacent(n) =
    let val optAdj = peekTableValue(adjList, n)
        (*val _ = print "########### Calculando adjacencias ########### \nSelectStack:"
        val _ = List.app (fn s => print (s ^ " - ")) (!selectStack)
        val _ = print "\ncoalescedNodes:"
        val _ = Set.app (fn c => print (c ^ " - ")) (!coalescedNodes)
        val _ = print "\nAdjacencias: "*)
    in case optAdj of
         SOME adj => ((*Set.app (fn a => print (a ^ " - ")) adj; print "\n"; *)Set.difference(adj, Set.union(listToSet(selectStack), !coalescedNodes)))
       | NONE     => (print "\n"; Set.empty String.compare)
    end

  fun enableMoves(nodes) =
    let fun enableMovesAux m =
          if inSet(m, activeMoves)
          then
            (removeElemNodeSet(activeMoves, m);
             updateSet(worklistMoves, m))
          else
            ()
    in
      Set.app (fn n => Set.app (fn m => enableMovesAux m) (nodeMoves(n))) nodes
    end 

  fun decrementDegree(m) =
    let val d = getDegree(m)
        val _ = updateTable(degree, m, fn _ => d-1)
    in
      if d = colorCount
      then
        (enableMoves(Set.add(adjacent(m) ,m));
         removeElemTempSet(spillWorklist, m);
         if moveRelated(m)
         then
           updateSet(freezeWorklist, m)
         else
           ((*print ("Se agrega en 2: " ^ m ^ "\n");*) updateSet(simplifyWorklist, m)))
      else
        ()
    end

  fun simplify() =
    case takeElem(simplifyWorklist) of
      SOME s => 
      let val _ = removeElemTempSet(simplifyWorklist, s)
          val _ = push(s,selectStack)
          val _ = print "Init adjacent to decrement 1\n\n"
          val _ = Set.app (fn t => print (t ^ " - ")) (adjacent(s))
          val _ = print "\n\nEnd adjacent to decrement 1\n\n"
      in
        Set.app decrementDegree (adjacent(s))
      end
    | NONE => ()

  fun addWorkList(u) =
    if not(inSetNoRef(u, precolored)) andalso not(moveRelated(u)) andalso (getDegree(u) < colorCount)
    then
      (removeElemTempSet(freezeWorklist, u);
       (*print ("Se agrega en 5: " ^ u ^ "\n");*)
       updateSet(simplifyWorklist, u))
    else
      ()

  fun ok(t,r) =
    getDegree(t) < colorCount orelse inSetNoRef(t, precolored) orelse inSet((t,r), adjSet)

  fun conservative(nodes) =
    let val k = ref 0
        val _ = Set.app (fn n => if getDegree(n) >= colorCount then k := !k + 1 else ()) nodes
    in !k < colorCount
    end

  fun getAlias(n) =
    if inSet(n, coalescedNodes)
    then
      getAlias(getTableValue(alias, n))
    else
      n

  fun combine(u,v) =
    let val _ = if inSet(v, freezeWorklist)
                then
                  removeElemTempSet(freezeWorklist, v)
                else
                  removeElemTempSet(spillWorklist, v)
        val _ = updateSet(coalescedNodes, v)
        val _ = updateTable(alias, v, fn _ => u)
        val _ = updateSetTable(moveList, u, getTableValue(moveList, v))
        val _ = enableMoves(singleTempSet v)
        (*val _ = print ("Combinando " ^ u ^ " <---> " ^ v ^ "\n")*)
        val _ = Set.app (fn t => (addEdge(t,u); decrementDegree(t))) (adjacent(v))
        val _ = print "Init adjacent to decrement 2\n\n"
        val _ = Set.app (fn t => print (t ^ " - ")) (adjacent(v))
        val _ = print "\n\nEnd adjacent to decrement 2\n\n"
    in
      if getDegree(u) >= colorCount andalso inSet(u, freezeWorklist)
      then
        (removeElemTempSet(freezeWorklist, u);
         updateSet(spillWorklist, u))
      else
        ()
    end

  fun coalesce() =
    case takeElem(worklistMoves) of
      SOME m =>  
        (let (*val _ = (printNode m; print "\n")*)
            val (x,y) = getTableValue(movesPair, m)
            (*val _ = print ("DEAD 124\n("^ x ^","^y^")")*)
            val (x,y) = (getAlias(x), getAlias(y))
            val (u,v) = if inSetNoRef(y, precolored) then (y,x) else (x,y)
            val _ = removeElemNodeSet(worklistMoves,m)
            val _ = print ("\n(U,V) = ("^ u ^","^v^")\n")
            (*val _ = print "Lista de adjacencia:\n"
            val _ = Table.app (fn (t,s) => (print ("temporario: "^t^"\nconj. de adjacencia: "); Set.app (fn x => print (x ^ " - ")) s; print "\n")) (!adjList)*)
            (*val _ = print ("(u,v) in AdjSet: " ^ Bool.toString(inSet((u,v), adjSet)) ^ "\n")*)
        in
          if u = v
          then
            ((*print "DEAD 132\n";*)
              updateSet(coalescedMoves, m);
             addWorkList(u)(*;
             print "DEAD 128\n"*))
          else
            ((*print "DEAD 135\n";*)if inSetNoRef(v, precolored) orelse inSet((u,v), adjSet)
                        then
                          ((*print "DEAD 133\n";*)
                            updateSet(constrainedMoves, m);
                           addWorkList(u);
                           addWorkList(v)(*;
                           print "DEAD 129\n"*))
                        else
                          ((*print "DEAD 136\n";*)if (inSetNoRef(u, precolored) andalso ((*print "DEAD 1361\n"; print ("v: "^ v ^"\n") ;*) Set.foldl (fn (x,r) => ok(x,u) andalso r) true (adjacent(v))))
                                                       orelse ((*print "DEAD 1363\n";*) not(inSetNoRef(u, precolored)) andalso conservative(Set.union(adjacent(u), adjacent(v))))
                                                    then
                                                      ((*print "DEAD 134\n";*)
                                                       updateSet(coalescedMoves, m);
                                                       (*print("Nodos coalescidos: " ^ u ^ " --- " ^ v ^ "\n");*)
                                                       combine(u, v);
                                                       addWorkList(u)(*;
                                                       print "DEAD 130\n"*))
                                                    else
                                                      ((*print "DEAD 131\n";*)updateSet(activeMoves, m))))
        end; print "SimplifyWL:\n"; Set.app (fn x => print(x ^ " - ")) (!simplifyWorklist);
        print "\nSpillWL:\n"; Set.app (fn x => print(x ^ " - ")) (!spillWorklist); print "\n")
 
    | NONE => ()

  fun freezeMoves(u) =
    let fun aux(m) =
      let val (x,y) = getTableValue(movesPair, m)
          (*val _ = print "DEAD 333333333333333\n"*)
          val v = if getAlias(y) = getAlias(u) then getAlias(x) else getAlias(y)
          val _ = removeElemNodeSet(activeMoves, m)
          val _ = updateSet(frozenMoves, m)
          (*val _ = print "DEAD 444444444444444\n"*)
      in 
        if Set.isEmpty(nodeMoves(v)) andalso getDegree(v) < colorCount
        then
          (removeElemTempSet(freezeWorklist, v);
           (*print ("Se agrega en 3: " ^ u ^ "\n");*)
           updateSet(simplifyWorklist, u))
        else
          ()
      end
    in Set.app aux (nodeMoves(u))
    end

  fun freeze() =
    case takeElem(freezeWorklist) of
      SOME u => (removeElemTempSet(freezeWorklist, u);
                 updateSet(simplifyWorklist, u);
                 freezeMoves(u))
    | NONE => ()

  fun heuristicCost(t : tigertemp.temp, cost : (tigertemp.temp, int) Table.dict ref) =
    case Table.peek(!cost,t) of
      SOME n => let val c = (Real.fromInt(n)/Real.fromInt(getDegree(t)))
                in print ("temporario: " ^ t ^ "--- costo: " ^ Real.toString c ^ "\n") ; SOME c
                end
    | NONE => NONE


  fun compareSpillCost( a : real option, b : real option) : bool =
    case (a,b) of
      (SOME va, SOME vb) => va < vb
    | (SOME va, NONE)    => true
    | _                  => false


  (*fun heuristicCost2(t : tigertemp.temp, cost : (tigertemp.temp, int) Table.dict ref) =
    case Table.peek(!cost,t) of
      SOME n => Real.fromInt(n)/Real.fromInt(getDegree(t))
    | NONE => 1000000.0*)
  
  (*fun selectSpill(cost) =
      case takeElem(spillWorklist) of
        SOME m => 
          let val _ = print "spillWorklist:\n"
              val _ = Set.app (fn t => print (t ^ " - ")) (!spillWorklist)
              val _ = print "\n"
              val _ = (print "COSTOS \n" ; 
                      Table.app (fn (x,y) => print ("( " ^ x ^ ", " ^ Int.toString y ^ ") - ")) (!cost);
                      print "\n")
              val _ = print ("VALOR A ESPILAR " ^ m ^ "\n")
          in (removeElemTempSet(spillWorklist, m);
              updateSet(simplifyWorklist, m);
              freezeMoves(m))
          end
      | NONE => ()
  *)

  fun selectSpill(cost: (tigertemp.temp, int) Table.dict ref) =
    let val _ = print "spillWorklist:\n"
        val _ = Set.app (fn t => print (t ^ " - ")) (!spillWorklist)
        val _ = print "\n"
        val _ = (print "COSTOS \n" ; 
                Table.app (fn (x,y) => print ("( " ^ x ^ ", " ^ Int.toString y ^ ") - ")) (!cost);
                print "\n")
        val min = Set.foldl (fn (x,r) => let val d = heuristicCost (x,cost)
                                         in case r of
                                              SOME (y,c) => if compareSpillCost (d,c)
                                                            then SOME (x,d)
                                                            else SOME (y,c)
                                            | NONE => SOME (x,d)
                                         end) NONE (!spillWorklist)
    in
      case min of (*takeElem(spillWorklist)*)
        SOME (m,_) => (print ("VALOR A ESPILAR " ^ m ^ "\n");
                      print(Bool.toString(inSet(m, spillWorklist))); print ("\n");
                      removeElemTempSet(spillWorklist, m);
                      (*print ("Se agrega en 4: " ^ m ^ "\n");*)
                      updateSet(simplifyWorklist, m);
                      freezeMoves(m))
      | NONE => ()
    end

  fun assignColors() =
    ((while not(null(!selectStack)) do
        let (*val _ = print "DEAD 333 \n"*)
            (*val _ = List.app (fn x => ((print "---------> Select "); (print ("("^x^")")); (print "\n"))) (!selectStack)*)
            val n = pop(selectStack)
            (*val _ = List.app (fn x => ((print "---------> Select "); (print ("("^x^")")); (print "\n"))) (!selectStack)*)
            val _ = print "DEAD 444 \n"
            val okColorList = [0,1,2,3,4,5,6,7,8,9,10]   (*[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12]*)
            val okColors = ref (Set.addList((Set.empty Int.compare), okColorList))
            val _ = print "DEAD 555 \n"
            fun aux(w) =
              if Set.member(Set.union(!coloredNodes, precolored), getAlias(w))
              then
                case peekTableValue(color,getAlias(w)) of
                  SOME t => removeElemIntSet(okColors, t)
                | NONE   => ()
                (*(print "BBBBBBB"; print (getAlias(w)); removeElemIntSet(okColors, getTableValue(color, getAlias(w))))*)
              else
                ()
            val nAdj = peekTableValue(adjList, n)
            val _ = print "DEAD 666 \n"
            val _ = case nAdj of
                      SOME adj => (Set.app aux adj; print ("OK colors: \n"); Set.app (fn x => print ((Int.toString x) ^ " -- ")) (!okColors); print "\n")
                    | NONE     => ()
            val _ = print "DEAD 777 \n"
        in
          (if Set.isEmpty(!okColors)
                    then
                      (print ("Posible spill: " ^ n ^ "\n"); updateSet(spilledNodes, n))
                    else
                      (updateSet(coloredNodes, n);
                       case takeElem(okColors) of
                         SOME c => (print ("Se colorea a "^ n ^ " con " ^ (Int.toString c) ^"\n"); updateTable(color, n, fn _ => c))
                       | NONE => ()); print "AAAAAAAAAAAAA")
        end);
        print "Alias:\n";
        Table.app (fn (t1,t2) => print (t1 ^ " - " ^ t2 ^ "\n")) (!alias);
        Table.app (fn (k,x) => ((print "Colores"); (print ("("^k^","^Int.toString x^")")); (print "\n"))) (!color);
        (Set.app (fn n => (print (n^"   "^getAlias(n)^" \n");updateTable(color, n, fn _ => getTableValue(color, getAlias(n))))) (!coalescedNodes)))


  fun printInterferenceGraph() =
    let
      val _ = print "\n\n\n############### Inicio grafo interferencia ###############\n"
      val _ = Set.app (fn x => print("\""^x^"\" ")) (!initial)
      val _ = print "\n"
      val _ = Set.app (fn (x,y) => print ("\""^x^"\"--\""^y^"\"\n")) (!adjSet)
      val _ = print "edge [style=dashed]\n"
      val _ = Set.app (fn x => let val (a,b) = getTableValue(movesPair, x) in print("\""^a^"\"--\""^b^"\"[color=red]\n") end) (!worklistMoves)
      val _ = print "############### Fin grafo interferencia ###############\n\n\n"
    in
      ()
    end

  fun initializeColoring(newTemps) =
    let
      val _ = spilledNodes := Set.empty String.compare
      val _ = initial := Set.union (Set.union(!coloredNodes, !coalescedNodes), newTemps)
      val _ = coalescedNodes := Set.empty String.compare
      val _ = coloredNodes := Set.empty String.compare
      (*val _ = color := (#1 (List.foldl (fn (r, (res,n)) => (Table.insert (res, r, n),n+1)) (Table.mkDict String.compare, 0) tigerframe.allRegs))*)
      val _ = alias := Table.mkDict String.compare
      val _ = moveList := Table.mkDict String.compare
      val _ = worklistMoves := Set.empty compareNodes
      val _ = adjSet := Set.empty adjSetCompare
      val _ = adjList := Table.mkDict String.compare
      val _ = degree := Table.mkDict String.compare
      val _ = spillWorklist := Set.empty String.compare
      val _ = activeMoves := Set.empty compareNodes
      val _ = freezeWorklist := Set.empty String.compare
      val _ = simplifyWorklist := Set.empty String.compare
      val _ = movesPair := Table.mkDict tigergraph.compareNodes
      val _ = constrainedMoves := Set.empty compareNodes
      val _ = frozenMoves := Set.empty compareNodes
      val _ = selectStack := []
      val _ = coalescedMoves := Set.empty compareNodes
    in
      ()
    end

  fun coloring {code = code, initial = init, spillCost = cost, registers = regs } =
    let val flowGraph = livenessAnalysis(code)
        (*val _ = print "Empieza el grafo de flujo\n\n\n"
        val _ = List.app (fn n => printNodeExt n) (nodes (#control flowGraph))
        val _ = print "Termina el grafo de flujo\n\n\n"*)
        fun printSelect (s) =
          let val _ = print ("\n\n\n-------------> Inicio SelectStack " ^ s ^ "<------------- \n\n" )
              val _ = List.app (fn t => print (t ^ " - ")) (!selectStack)
              val _ = print "\n\n-------------> Fin SelectStack <------------- \n\n\n"
          in () end
        fun printSimplify (s) =
          let val _ = print ("\n\n\n-------------> Inicio simplifyWorklist " ^ s ^ "<------------- \n\n" )
              val _ = Set.app (fn t => print (t ^ " - ")) (!simplifyWorklist)
              val _ = print "\n\n-------------> Fin simplifyWorklist <------------- \n\n\n"
          in () end
        fun printAdjList (s) =
          let val _ = print ("\n\n\n-------------> Inicio adjList " ^ s ^ "<------------- \n\n" )
              val _ = Table.app (fn (t,s) => (print ("temporario: "^t^"\nconj. de adjacencia: "); Set.app (fn x => print (x ^ " - ")) s; print "\n")) (!adjList)
              val _ = print "\n\n-------------> Fin adjList <------------- \n\n\n"
          in () end
        (*val _ = print "Inicia lista adjacencia 1\n"
        val _ = printAdjList("")
        val _ = print "Fin lista adjacencia 1\n"*)
        val _ = build(flowGraph)
        (*val _ = printInterferenceGraph()*)
        val _ = makeWorkList()
        val _ = print ("----------- DEAD 222222222222222" ^ Int.toString colorCount)
        val _ = print "---------------------> Al inicio spilledNodes <---------------------\n"
        (*val _ = printSelect()*)
        val _ = (Set.app (fn sn => print (sn ^ " - ")) (!spilledNodes) ; print "\n")
        val _ = initialColor()
        val _ = print "Inicia lista adjacencia\n"
        val _ = printAdjList("")
        val _ = print "Fin lista adjacencia\n"
        fun iterationBody() =
          if not(Set.isEmpty(!simplifyWorklist))
          then (simplify(); printSimplify(""); printSelect("Luego simplify"))
          else if not(Set.isEmpty(!worklistMoves))
               then ((*print "DEAD 4141511 \n";*) coalesce())
               else if not(Set.isEmpty(!freezeWorklist))
                    then ((*print "DEAD 44444444 \n";*) freeze())
                    else if not(Set.isEmpty(!spillWorklist))
                         then ((*print "DEAD 55555555 \n";*) selectSpill(cost)) (*spillWorklist := (Set.empty String.compare))*)
                         else (((*print "DEAD 66666666 \n"*)) )
        fun iteration() =
          (iterationBody();
           if (Set.isEmpty(!simplifyWorklist) andalso
               Set.isEmpty(!worklistMoves) andalso 
               Set.isEmpty(!freezeWorklist) andalso 
               Set.isEmpty(!spillWorklist))
           then ()
           else iteration())
        val _ = iteration()
        val _ = print "Fin iteración\n"; 
        (*val _ = color := (#1 (List.foldl (fn (r, (res,n)) => (Table.insert (res, r, n),n+1)) (Table.mkDict String.compare, 0) tigerframe.allRegs))*)
        val _ = (print "Colores iniciales:" ; Table.app (fn (x,y) => print ("(" ^ x ^ ", " ^ Int.toString y ^ ")")) (!color))
        val _ = printSelect("Antes assignColors")
        val _ = assignColors()
        val _ = print "Fin de assignColors \n"; 
        (*val _ = print "########### Calculando adjacencias ########### \nSelectStack:"
        val _ = List.app (fn s => print (s ^ " - ")) (!selectStack)
        val _ = print "\ncoalescedNodes:"
        val _ = Set.app (fn c => print (c ^ " - ")) (!coalescedNodes)
        val _ = print "\nAdjacencias: "
        val _ = (Set.app (fn a => print (a ^ " - ")) (Table.find(!adjList, "T12")); print "\n")*)
        fun intToReg (n) =
          case List.find (fn (_,y) => y = n) colores of
            SOME (x,_) => x
          | NONE => raise Fail ("error: coloreo " ^ Int.toString n)
          (*if (n >= 0) andalso (n < colorCount+5)
          then List.nth(tigerframe.allRegs, n)
          else raise Fail ("error: coloreo " ^ Int.toString n)*)
       val coloreo = Table.map (fn (r,n) => intToReg(n)) (!color)
       val _ = print "---------------------> Al final spilledNodes <---------------------\n"
       val _ = (Set.app (fn sn => print (sn ^ " - ")) (!spilledNodes) ; print "\n")
    in (coloreo, Set.listItems (!spilledNodes)) end
end