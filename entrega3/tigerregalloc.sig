signature tigerregalloc =
sig
  
  val alloc : tigerassem.instr list * tigerframe.frame -> tigerassem.instr list * tigercolor.allocation

end