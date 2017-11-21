structure tigertemp :> tigertemp = struct
type label = string
type temp = string
type nodeName = string
fun makeString s = s
local
	val i = ref 0
	val j = ref 0
	val k = ref 0
in
	fun newtemp() =
		let
			val s = "T"^Int.toString(!i)
		in
			i := !i+1;
			s
		end
	fun newlabel() =
		let
			val s = "L"^Int.toString(!j)
		in
			j := !j+1;
			s
		end
  fun newNodeName() =
		let
			val s = "N"^Int.toString(!k)
		in
			k := !k+1;
			s
		end

	fun compare(a,b) = 
		String.compare(a,b)

end

end
