(*
	Frames para el 80386 (sin displays ni registers).

		|    argn    |	fp+4*(n+1)
		|    ...     |
		|    arg2    |	fp+16
		|    arg1    |	fp+12
		|	fp level |  fp+8
		|  retorno   |	fp+4
		|   fp ant   |	fp
		--------------	fp
		|   local1   |	fp-4
		|   local2   |	fp-8
		|    ...     |
		|   localn   |	fp-4*n
*)

structure tigerframe :> tigerframe = struct

open tigertemp

type level = int

val fp = string.temp "FP"				(* frame pointer *)
val argregs = ["A","B"]

val sp = "SP"				(* stack pointer *)
val rv = "RV"				(* return value  *)
val ov = "OV"				(* overflow value (edx en el 386) *)
val wSz = 4					(* word size in bytes *)
val log2WSz = 2				(* base two logarithm of word size in bytes *)
val fpPrev = 0				(* offset (bytes) *)
val fpPrevLev = 2*wSz			(* offset (bytes) *)
val argsInicial = 3*wSz			(* words *)

val argsDelta = wSz

val argsOffInicial = 0		(* words *)
val argsGap = wSz			(* bytes *)
val regInicial = 1			(* reg *)
val localsInicial = ~1		(* words *)

val localsDelta = ~wSz

val localsGap = ~4 			(* bytes *)
val calldefs = [rv]
val specialregs = [rv, fp, sp]
val argregs = []
val callersaves = []
val calleesaves = []

type frame = {
	name: string,
	formals: bool list,
	locals: bool list,
	actualArg: int ref,
	actualLocal: int ref,
        actualArgRegs: temp.list ref
}
type register = string
datatype access = InFrame of label | InReg of tigertemp.temp

(* cada función genera el tipo siguiente *)

datatype frag = PROC of {body: tigertree.stm, frame: frame}
	| STRING of tigertemp.label * string
fun newFrame{name, formals} = {
	name=name,
	formals=formals,
	locals=[],
	actualArg=ref argsInicial,
	actualLocal=ref localsInicial,
	actualArgRegs=ref argregs
}
fun name(f: frame) = #name f
fun string(l, s) = l^tigertemp.makeString(s)^"\n"
fun formals({formals=f, ...}: frame) = 
	let	fun aux(n, []) = []
		| aux(n, h::t) = InFrame(n)::aux(n+argsGap, t)
	in aux(argsInicial, f) end
fun maxRegFrame(f: frame) = !(#actualReg f)

(* alocamos un nuevo argumento *)
fun allocArg (f: frame) b = 
    if b then
        InFrame(!(#actualArg(f))*wSz+argsOffIncial)
        before #actualArg(f) := !(#actualArg(f))+1
    else (* registro o stack *)
        if not(null(!(#actualArgRegs(f)))) then
            InReg(hd(!(#actualArgRegs(f))))
            before #actualArgRegs(f) := tl(!(#actualArgRegs(f)))
        else (* se terminaron los registros *)
            InFrame(!(#actualArg(f)))
            before #actualArg(f) := !(#actualArg(f))+1

fun allocLocal (f:frame) b =
    if b then (* memoria *)
        InFrame (!(#actualLocal(f))*wSz)
        before #actualLocal(f) := !(#actualLocal(f))+localDelta
    else InReg (newtemp())

(* código intermedio para acceder a su valor según su access *)
fun exp (InReg t) = temp t
  | exp(InFrame off) = Mem(BinOp(Plus,temp ff,Conet off))

fun procEntryExit1(f,e) = e
fun procEntryExit2(frame,body) =
    body@(tigerassem.Oper{assem="",src[rv,rf,ff]@callee_saves,drt=[],jump=NONE})



fun exp(InFrame k) e = MEM(BINOP(PLUS, TEMP(fp), CONST k))
| exp(InReg l) e = TEMP l
fun externalCall(s, l) = CALL(NAME s, l)

end
