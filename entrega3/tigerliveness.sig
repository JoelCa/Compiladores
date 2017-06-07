signature tigerliveness =
sig
  type igraph

  val interferenceGraph : tigerflow.flowgraph -> igraph * ((tigertemp.temp list) tigergraph.table)

  (*val show : outstream * igraph -> unit*)
end