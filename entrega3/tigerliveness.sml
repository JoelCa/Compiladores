structure tigerliveness :> tigerliveness =
struct
  open tigergraph
  open Splayset

  type liveSet = tigertemp.temp list
  type liveMap = liveSet tigergraph.table

  val inTemps  : (tigertemp.temp set) table ref = ref (mkDict (compareNodes))
  val outTemps : (tigertemp.temp set) table ref = ref (mkDict (compareNodes))
  val inResults  : (tigertemp.temp set) table ref = ref (mkDict (compareNodes))
  val outResults : (tigertemp.temp set) table ref = ref (mkDict (compareNodes))

  fun liveOuts ({control = fg, use = u, def = d, ...}) flag = 
    let val ns = nodes fg
        val _ = if flag
                then foldl (fn (x,_) => T.insert ((!inTemps), x, (empty String.compare)) ; T.insert ((!outTemps), x, (empty String.compare))) () ns
                else ()
        val _ = foldl (fn (n,_) => body n) () ns
        fun body n = let val _ = T.insert ((!inResults), n, find ((!inTemps), n))
                         val _ = T.insert ((!outResults), n, find ((!outTemps), n))
                         val _ = T.insert ((!inTerms), n, union (find (u, n)))


  (*fun interferenceGraph g = *)
(*
{ control: graph,
  def: tigertemp.temp list table,
  use: tigertemp.temp list table,
  ismove: bool table }
*)
end