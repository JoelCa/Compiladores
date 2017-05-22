structure tigerflow =
struct
  open tigergraph

  (*structure G = tigergraph*)
  
  type flowgraph = { control: graph,
                     def: tigertemp.temp list table,
                     use: tigertemp.temp list table,
                     ismove: bool table }
end