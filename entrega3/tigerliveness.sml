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

  fun initialize() = 
    let val _ = inTemps    := T.mkDict (compareNodes) (* in *)
        val _ = outTemps   := T.mkDict (compareNodes) (* out *)
        val _ = inResults  := T.mkDict (compareNodes) (* in' *)
        val _ = outResults := T.mkDict (compareNodes) (* out' *)
    in () end

  fun liveOutsAux ({control = fg, use = u, def = d, ismove = m}) flag = 
    let val ns = rev (nodes fg)
        val _ = 
          if flag
          then List.app (fn x => (insertTable (inTemps, x, (empty String.compare))
                                  ; insertTable (outTemps, x, (empty String.compare)))) ns
          else ()
        fun body (n:node) = 
          let val _ = insertTable (inResults, n, T.find (!inTemps, n))
              val _ = insertTable (outResults, n, T.find (!outTemps, n))
              val _ = insertTable (inTemps, n, union (T.find (u, n), difference (T.find (!outTemps, n), T.find (d, n))))
              val _ = insertTable (outTemps, n, List.foldl (fn (s,r) => union (T.find (!inTemps, s), r)) (empty String.compare) (succ(n)))
          in 
            ()
          end
        val _ = List.app body ns
    in
      if List.foldr (fn (n,r) => equal (T.find (!inResults, n), T.find (!inTemps, n)) andalso
                                 equal (T.find (!outResults, n), T.find (!outTemps, n)) andalso
                                 r) true ns
      then
        !outTemps
      else
        liveOutsAux ({control = fg, use = u, def = d, ismove = m}) false
    end

  fun liveOuts ({control = fg, use = u, def = d, ismove = m}) = 
    liveOutsAux ({control = fg, use = u, def = d, ismove = m}) true
end