structure tigercolor :> tigercolor = 
struct
  structure T = Splaymap

  type allocation = (tigerframe.register, tigertemp.temp) T.dict

  fun color _ = (Splaymap.mkDict  String.compare, [])

end