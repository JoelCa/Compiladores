signature tigerliveness =
sig
  type igraph

  type liveSet = tigertemp.temp Splayset.set
  type liveMap = liveSet tigergraph.table

  val liveOuts : tigerflow.flowgraph -> liveMap

  (*val interferenceGraph : tigerflow.flowgraph -> igraph * ((tigertemp.temp list) tigergraph.table)*)

  (*val show : outstream * igraph -> unit*)
end