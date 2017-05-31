structure tigerliveness :> tigerliveness =
struct
  open tigergraph
  open Splayset

  datatype igraph =
    IGraph of {graph: tigergraph.graph,
               tnode: tigertemp.temp -> tigergraph.node,
               gtemp: tigergraph.node -> tigertemp.temp,
               moves: (tigergraph.node * tigergraph.node) list}

  type liveSet = tigertemp.temp list
  type liveMap = liveSet tigergraph.table

  val inTemps  : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes))   (* in *)
  val outTemps : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes))   (* out *)
  val inResults  : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes)) (* in' *)
  val outResults : (tigertemp.temp set) table ref = ref (T.mkDict (compareNodes)) (* out' *)

  fun liveOuts ({control = fg, use = u, def = d, ismove = m}) flag = 
    let val ns = nodes fg
        val _ = if flag
                then List.app (fn x => (T.insert (!inTemps, x, (empty String.compare)) ; T.insert (!outTemps, x, (empty String.compare)); ())) ns
                else ()
        fun body (n:node) = let val _ = T.insert (!inResults, n, T.find (!inTemps, n))
                         val _ = T.insert (!outResults, n, T.find (!outTemps, n))
                         val _ = T.insert (!inTemps, n, union (T.find (u, n), difference (T.find (!outTemps, n), T.find (d, n))))
                         val _ = T.insert (!outTemps, n, List.foldl (fn (s,r) => union (T.find (!inTemps, s), r)) (empty String.compare) (succ(n)))
                     in 
                      ()
                     end
        val _ = List.app body ns
        
    in
      if List.foldr (fn (n,r) => equal (T.find (!inResults, n), T.find (!inTemps, n))
                            andalso equal (T.find (!outResults, n), T.find (!outTemps, n)) andalso r) true ns
      then
        (!inTemps, !outTemps)
      else
        liveOuts ({control = fg, use = u, def = d, ismove = m}) false
    end

  fun interferenceGraph ({control = fg, use = u, def = d, ismove = m}) = 
    let val ns = nodes fg
        val (lin, lout) = liveOuts ({control = fg, use = u, def = d, ismove = m}) true
        val ig = foldl (fn (n, g) => newNode (g,n)) (newGraph ()) ns
        val _ = app body ns
        fun body n =
          if T.find(m, n)
          then mk_edge
          else
    in
    end
(*
{ control: graph,
  def: tigertemp.temp list table,
  use: tigertemp.temp list table,
  ismove: bool table }
*)

  datatype igraph =
    IGraph of {graph: tigergraph.graph,
               tnode: tigertemp.temp -> tigergraph.node,
               gtemp: tigergraph.node -> tigertemp.temp,
               moves: (tigergraph.node * tigergraph.node) list}
end