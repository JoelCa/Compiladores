signature tigercodegen =
sig
    val codegen : tigerframe.frame -> tigertree.stm -> tigerassem.instr list
    val maximalMunch : tigerframe.frame -> tigertree.stm list -> tigerassem.instr list
end
