signature tigermg =
sig
  val instr2graph : tigerassem.instr list -> tigerflow.flowgraph * tigergraph.node list
end