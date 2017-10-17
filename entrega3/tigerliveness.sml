structure tigerliveness :> tigerliveness =
struct
  open tigergraph
  open Splayset
  open Splaymap

  datatype igraph =
    IGraph of {graph: tigergraph.graph,
               tnode: (tigertemp.temp, tigergraph.node) dict ref,
               gtemp: (tigergraph.node, tigertemp.temp) dict ref,
               moves: (tigergraph.node * tigergraph.node) list}

  type liveSet = tigertemp.temp set
  type liveMap = liveSet tigergraph.table

  val inTemps  : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes))   (* in *)
  val outTemps : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes))   (* out *)
  val inResults  : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes)) (* in' *)
  val outResults : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes)) (* out' *)

  fun insertTable(t,k,v) =
    t := T.insert(!t, k, v)

  fun liveOutsAux ({control = fg, use = u, def = d, ismove = m}) flag = 
    let val ns = nodes fg
        val _ = 
          if flag
          then List.app (fn x => (insertTable (inTemps, x, (empty String.compare))
                                ; insertTable (outTemps, x, (empty String.compare)))) ns
          else ()
        fun body (n:node) = 
          let val _ = T.app (fn (k,x) => ((printNode k); (print "\n"))) (!inTemps)
              val _ = insertTable (inResults, n, T.find (!inTemps, n))
              val _ = print "DEAD 777111"
              val _ = insertTable (outResults, n, T.find (!outTemps, n))
              val _ = print "DEAD 777"
              val _ = insertTable (inTemps, n, union (T.find (u, n), difference (T.find (!outTemps, n), T.find (d, n))))
              val _ = print "DEAD 777123"
              val _ = insertTable (outTemps, n, List.foldl (fn (s,r) => union (T.find (!inTemps, s), r)) (empty String.compare) (succ(n)))
              val _ = print "DEAD 77722"
          in 
            ()
          end
        val _ = List.app body ns
        
    in
      if List.foldr (fn (n,r) => equal (T.find (!inResults, n), T.find (!inTemps, n))
                            andalso equal (T.find (!outResults, n), T.find (!outTemps, n)) andalso r) true ns
      then
        !outTemps
      else
        liveOutsAux ({control = fg, use = u, def = d, ismove = m}) false
    end

  fun liveOuts fg = liveOutsAux fg true

  (*TERMINAR*)
  fun interferenceGraph ({control = fg, use = u, def = d, ismove = m}) =
    let val ns = nodes fg
        val lout = liveOuts ({control = fg, use = u, def = d, ismove = m})
        
        val ig = newGraph ()
        val itn = ref (Splaymap.mkDict (String.compare))
        val igt = ref (Splaymap.mkDict compareNodes)
        val moves = ref []

        fun getNode a = case Splaymap.peek(!itn,a) of
                          SOME x => x 
                        | NONE   => let val y = newNode ig
                                    in itn := Splaymap.insert (!itn, a, y);
                                       igt := Splaymap.insert (!igt, y, a);
                                       y
                                    end

        fun moveEdge (n, na, b) =
          if member (T.find (u, n), b) 
          then ()
          else mk_edge (na, getNode b)

        fun body n =
          if T.find(m, n)
          then
            Splayset.app (fn a =>
                            let val na = getNode a
                                val _ = Splayset.app (fn c => moves := (na, getNode c) :: !moves) (T.find (u, n))
                            in Splayset.app (fn b => moveEdge (n, na, b)) (T.find (lout, n))
                            end) (T.find (d, n))
          else
            Splayset.app (fn a =>
                            let val na = getNode a
                            in Splayset.app (fn b => mk_edge (na, getNode b)) (T.find (lout, n))
                            end) (T.find (d, n))
        val _ = List.app body ns
    in
      (IGraph {graph = ig, tnode = itn, gtemp = igt, moves = !moves}, T.map (fn (k,s) => Splayset.listItems s) lout)
    end
end