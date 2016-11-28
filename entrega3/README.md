A realizar:
- Probar el interprete.
- Terminar el maximalMunch.
- Terminar el pretty printer de assembler.


Lo último que hicimos:
- Generar el "pretty printer" del assembler, a partir del codigo intermedio canonizado (Solo considerarmos el
fragmento PROC).
- Definimos el maximalMunch. Esta incompleto porque falta el munchStm del CALL:
  - Para esto vamos a tener que hacer la función munchArgs.


Posible error:
- Solamente probamos el pretty printer sobre ../tests/good/testEj.tig.
Y se puede ver que hay un salto al label L5, el cual no existe.