open tigerlex
open tigergrm
open tigerescap
open tigerseman
open tigercanon
open BasicIO Nonstdio
open tigerinterp

fun lexstream(is: instream) =
	Lexing.createLexer(fn b => fn n => buff_input is b 0 n);
fun errParsing(lbuf) = (print("Error en parsing!("
	^(makestring(!num_linea))^
	")["^(Lexing.getLexeme lbuf)^"]\n"); raise Fail "fin!")
fun main(args) =
	let	fun arg(l, s) =
			(List.exists (fn x => x=s) l, List.filter (fn x => x<>s) l)
		val (arbol, l1)		= arg(args, "-arbol")
		val (escapes, l2)	= arg(l1, "-escapes") 
		val (ir, l3)		= arg(l2, "-ir") 
		val (canon, l4)		= arg(l3, "-canon") 
		val (code, l5)		= arg(l4, "-code") 
		val (flow, l6)		= arg(l5, "-flow") 
		val (inter, l7)		= arg(l6, "-inter") 
		val entrada =
			case l7 of
			[n] => ((open_in n)
					handle _ => raise Fail (n^" no existe!"))
			| [] => std_in
			| _ => raise Fail "opcio'n dsconocida!"
		val lexbuf = lexstream entrada
		val expr = prog Tok lexbuf handle _ => errParsing lexbuf
		val _ = findEscape(expr)
		val _ = if arbol then tigerpp.exprAst expr else ()
    val _ = transProg(expr);
    val fragmentos = tigertrans.getResult()
                (* fun optionFilter [] = [] *)
                (*   | optionFilter ((SOME s) :: xs) = s :: optionFilter xs  *)
                (*   | optionFilter (NONE :: xs) = optionFilter xs *)
    val fcCanon = (tigercanon.traceSchedule o tigercanon.basicBlocks o tigercanon.linearize)

		(* Divide los fragmentos y canoniza los que son PROC *)
		fun divideFrags [] = ([],[])
		  | divideFrags (tigerframe.PROC {body,frame} :: t) = let val (stm,str) = divideFrags t in ((frame,fcCanon body)::stm,str) end
		  | divideFrags (tigerframe.STRING s :: t) = let val (stm,str) = divideFrags t in (stm,s::str) end

		val (canonizado, roData) = divideFrags fragmentos

		val _ = if canon then List.app (fn (f,b) => (print((tigerframe.name f)^":\n");List.app (print o tigerit.tree) b)) canonizado else ()
                                                                                                                                                      
    val (procs,strings) = tigertrans.procStringList(fragmentos)
                (* val stmList = optionFilter (map (tigertrans.procBody) fragmentos) *)
    val stmCanonList = map (fn (s,f) => (traceSchedule (basicBlocks (linearize s)), f)) procs
                (* val functionInstrCode = map (fn (s,f) => tigercodegen.maximalMunch f s) stmCanonList *)
		val _ = if ir then print(tigertrans.Ir(fragmentos)) else ()
                (* val _ = if code then map (map (print o (tigerassem.format (fn a => "")))) functionInstrCode else [[()]] *)
                val _ = if inter then tigerinterp.inter true stmCanonList strings else ()
	in
		print "yes!!\n"
	end	handle Fail s => print("Fail: "^s^"\n")

val _ = main(CommandLine.arguments())                          

            (* maximalMunch f (traceSchedule (basicBlocks (linearize b)))*)
