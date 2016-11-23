signature topsort =
sig

exception Ciclo
 
val topsort : (''a * ''a) list -> ''a list

end
