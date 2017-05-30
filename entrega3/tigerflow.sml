structure tigerflow =
struct
  open tigergraph
  open Splayset
  
  (*structure G = tigergraph*)
  
  type flowgraph = { control: graph,
                     def: tigertemp.temp set table,
                     use: tigertemp.temp set table,
                     ismove: bool table }
end