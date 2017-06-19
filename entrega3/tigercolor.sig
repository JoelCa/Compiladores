signature tigercolor =
sig

  structure T : Splaymap

  type allocation

  val color : { interference: tigerliveness.igraph,
                initial: allocation,
                spillCost: tigergraph.node -> int,
                registers: tigerframe.register list
              } 
              -> allocation * tigertemp.temp list
end