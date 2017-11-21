signature tigertemp = sig
	type label = string
	type temp = string
  type nodeName = string
	val makeString: string -> string
	val newtemp: unit -> temp
	val newlabel: unit -> label
  val newNodeName : unit -> nodeName
  val compare : (temp * temp) -> order
end
