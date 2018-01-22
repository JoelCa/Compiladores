signature tigerliveness =
sig
  datatype igraph =
    IGraph of {graph: tigergraph.graph,
               tnode: (tigertemp.temp, tigergraph.node) Splaymap.dict ref,
               gtemp: (tigergraph.node, tigertemp.temp) Splaymap.dict ref,
               moves: (tigergraph.node * tigergraph.node) list}


  type liveSet = tigertemp.temp Splayset.set
  type liveMap = liveSet tigergraph.table

  val liveOuts : tigerflow.flowgraph -> liveMap

  val initialize : unit -> unit

end