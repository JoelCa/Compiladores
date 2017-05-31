signature tigerliveness =
sig
  type igraph

  val interferenceGraph : tigerflow.flowgraph -> igraph * (tigergraph.node -> tigertemp.temp list)

  (*val show : outstream * igraph -> unit*)
end