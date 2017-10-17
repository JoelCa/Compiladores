signature tigercolor =
sig
  structure Table : Splaymap
  type allocation = (tigertemp.temp, tigerframe.register) Table.dict

  val coloring : { code: tigerassem.instr list,
                   initial: allocation,
                   spillCost: tigergraph.node -> int,
                   registers: tigerframe.register list
                 }
                -> allocation * tigertemp.temp list

  val emptyAll : allocation
  val insertAll : allocation * tigertemp.temp * tigerframe.register -> allocation
  val findAll : allocation * tigertemp.temp -> tigerframe.register

end