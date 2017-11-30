signature tigercolor =
sig
(*  structure Table : Splaymap
  type allocation = (tigertemp.temp, tigerframe.register) Table.dict
*)
  type allocation
  
  val coloring : { code: tigerassem.instr list,
                   initial: allocation,
                   spillCost: (tigertemp.temp, int) Splaymap.dict ref,
                   registers: tigerframe.register list
                 }
                -> allocation * tigertemp.temp list

  val initializeColoring : tigertemp.temp Splayset.set -> unit
  val emptyAll : allocation
  val insertAll : allocation * tigertemp.temp * tigerframe.register -> allocation
  val findAll : allocation * tigertemp.temp -> tigerframe.register
  val printAll : allocation -> unit

end