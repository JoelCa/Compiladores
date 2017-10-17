structure tigergraph :> tigergraph =
struct

open tigertemp
open Splayset

exception GraphEdge

datatype node =
  Node of { name: string
          , successors : node set
          , predecessors : node set } ref

type graph = node list ref

fun printNode (Node n) = print (#name (!n))

fun nodes g = !g

fun succ (Node n) = listItems (#successors (!n))

fun pred (Node n) = listItems (#predecessors (!n))

(*NO se usa para grafos dirigidos*)
fun adj (Node n) = listItems (union (#predecessors (!n), #successors (!n)))

fun eq (Node n1, Node n2) = #name (!n1) = #name (!n2)

fun compareNodes (Node n1, Node n2) = String.compare (#name (!n1), #name (!n2))

fun newGraph () = ref []

fun newNode g =
  let val n = Node (ref {name = newNodeName (), successors = empty compareNodes, predecessors = empty compareNodes})
      val _ = g := (n :: (!g))
  in n
  end

fun mk_edge (Node n1 , Node n2) =
  let val _ = n1 := { name = #name (!n1)
                    , successors = add (#successors (!n1), Node n2)
                    , predecessors = #predecessors (!n1) }
      val _ = n2 := { name = #name (!n2)
                    , successors = #successors (!n2)
                    , predecessors = add (#predecessors (!n2), Node n1) }
  in ()
  end

fun rm_edge (Node n1 , Node n2) =
  if member (#predecessors (!n2), Node n1) andalso member (#successors (!n1), Node n2)
  then
    let val _ = n1 := { name = #name (!n1)
                      , successors = delete (#successors (!n1), Node n2)
                      , predecessors = #predecessors (!n1) }
        val _ = n2 := { name = #name (!n2)
                      , successors = #successors (!n2)
                      , predecessors = delete (#predecessors (!n2), Node n1) }
    in ()
    end
  else
    raise GraphEdge

fun nodename (Node n) = #name (!n)

structure T = Splaymap

type 'a table = (node, 'a) T.dict


end