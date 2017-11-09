signature tigergraph =
sig
  type graph
  type node
  
  val nodes: graph -> node list
  val succ: node -> node list
  val pred: node -> node list
  val adj: node -> node list
  val eq: node * node -> bool
  val newGraph: unit -> graph
  val newNode : graph -> node
  val compareNodes : node * node -> order
  val printNode : node -> unit
  val printNodeExt : node -> unit
  
  exception GraphEdge
  
  val mk_edge: node * node -> unit
  val rm_edge: node * node -> unit
  
  structure T : Splaymap
  type 'a table = (node, 'a) T.dict

  (*sharing type (node,'a) dict*)

  val nodename: node -> string (* for debugging *)
end