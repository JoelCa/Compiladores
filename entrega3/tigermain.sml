open tigerlex
open tigergrm
open tigerescap
open tigerseman
open tigercanon
open BasicIO Nonstdio
open tigerinterp
open tigerregalloc

fun lexstream(is: instream) =
	Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Error en parsing!("^
	                            (makestring(!num_linea))^
	                            ")["^(Lexing.getLexeme lbuf)^"]\n");
                        raise Fail "fin!")
fun instrCode {prolog = p, body = b : tigerassem.instr list, epilog = e} = 
  p ^ (foldr (fn (s, r) => (tigerassem.format tigertemp.makeString s) ^ r) "" b) ^ e
fun main(args) =
	let	fun arg(l, s) =
			(List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
		val (arbol, l1)		= arg(args, "-arbol")
		val (escapes, l2)	= arg(l1, "-escapes") 
		val (ir, l3)		  = arg(l2, "-ir") 
		val (canon, l4)		= arg(l3, "-canon") 
		val (code, l5)		= arg(l4, "-code") 
		val (flow, l6)		= arg(l5, "-flow") 
		val (inter, l7)		= arg(l6, "-inter") 
		val entrada =
			case l7 of
			  [n] => ((open_in n)
					handle _ => raise Fail (n^" no existe!"))
			| []  => std_in
			| _   => raise Fail "opcio'n desconocida!"
		val lexbuf = lexstream entrada
		val expr = prog Tok lexbuf handle _ => errParsing lexbuf
		val _ = findEscape(expr)
		
    val _ = if arbol then tigerpp.exprAst expr else ()

    val _ = transProg(expr);
    
    val fragmentos = ref NONE
    val canonCode = ref NONE

    val fcCanon = (tigercanon.traceSchedule o tigercanon.basicBlocks o tigercanon.linearize)

    fun getVal(a,f) = 
      case !a of
        SOME w => w
      | NONE   => let val x = f
                      val _ = a := SOME x
                  in x
                  end

    fun getFrag() = getVal(fragmentos, tigertrans.getResult())
    fun getCanonCode() = getVal(canonCode, tigertrans.procStringList fcCanon (getFrag()))
        
    val _ = if ir then print(tigertrans.Ir(getFrag())) else ()
    val _ = if canon 
            then List.app tigertrans.printProcString (getCanonCode())
            else ()
    val _ = if code
            then
              let val finalStrCode = tigertrans.procStringList2 (getCanonCode())
              in map print finalStrCode end
            else [()]
    val _ = if inter (* Funciona MAL *)
            then 
              let val (strings, procs) = tigertrans.splitEither (getCanonCode())
              in tigerinterp.inter true procs strings 
              end
            else ()
	in
		(*print "yes!!\n"*) ()
	end	handle Fail s => print("Fail: "^s^"\n")



val _ = main(CommandLine.arguments())