signature tigermg =
sig
  val instr2graph : tigerassem.instr list -> tigerflow.flowgraph * tigergraph.node list
  val initialize  : unit -> unit
end