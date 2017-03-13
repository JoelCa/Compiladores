(*
  Frames para el 80386 (sin displays ni registers).

    |    argn    |  fp+4*(n+1)
    |    ...     |
    |    arg2    |  fp+16
    |    arg1    |  fp+12
    |  fp level  |  fp+8   static link
    |  retorno   |  fp+4
    --------------
    |   fp ant   |  fp
    |   local1   |  fp-4
    |   local2   |  fp-8
    |    ...     |
    |   localn   |  fp-4*n

*)
(*
  Frame de ARM V7

    |    argn    |  fp+4*n
    |    ...     |
    |    arg2    |  fp+12
    |    arg1    |  fp+8
    |  fp level  |  fp+4   static link
    --------------
    |   fp ant   |  fp
    |   local1   |  fp-4
    |   local2   |  fp-8
    |    ...     |
    |   localn   |  fp-4*n
*)
structure tigerframe :> tigerframe = struct

open tigertree

type level = int

val fp             = "FP"          (* frame pointer *)
val sp             = "SP"          (* stack pointer *)
val rv             = "RV"          (* return value  *)
val ov             = "OV"          (* overflow value (edx en el 386) *)
val wSz            = 4             (* word size in bytes *)
val log2WSz        = 2             (* base two logarithm of word size in bytes *)
val fpPrev         = 0             (* offset (bytes) *)
val fpPrevLev      = 4             (* offset (bytes) *)
val argsInicial    = 0             (* words *)
val argsOffInicial = 1             (* words *)
val argsGap        = wSz           (* bytes *)
val regInicial     = 1             (* reg *)
val localsInicial  = 0             (* words *)
val localsGap      = ~4            (* bytes que indican el espacio entre el fp y el 1º local *)
val calldefs       = [rv]
val specialregs    = [rv, fp, sp]
val argregs        = ["r0","r1","r2","r3"]
val callersaves    = []
val calleesaves    = [] (*["r4","r5","r6","r7","r8","r9","r10","lr"]*)

datatype access = InFrame of int | InReg of tigertemp.label

type frame = {
    name: string,
    formals: bool list,
    locals: bool list,
    actualArg: int ref,
    actualLocal: int ref,
    actualReg: int ref,
    ftAccesos : access list ref
}
type register = string
datatype frag = PROC of {body: tigertree.stm, frame: frame}
              | STRING of tigertemp.label * string

fun newFrame{name, formals} = {
    name        = name,
    formals     = formals,
    locals      = [],
    actualArg   = ref argsInicial,
    actualLocal = ref localsInicial,
    actualReg   = ref (length argregs),           (* con la sugerencia de Guillermo *)
    ftAccesos   = ref [InFrame(fpPrevLev)]
}

fun name(f: frame) = #name f

fun string(l, s) = l^tigertemp.makeString(s)^"\n"

(* Los primeros 4 argumentos no escapados se guardarán en registro. *)
(* Luego se pondrán en memoria, como los argumentos escapados. *)
(* Agregamos un argumento escapado a la lista de formals, en representación del static link. *)
fun formals({formals=f,...}:frame) = let fun armaAccesos [] _ _                = []
                                           | armaAccesos (_::xs) [] n          = (InFrame (n*wSz))::armaAccesos xs [] (n+1)
                                           | armaAccesos (true::xs) rs n       = (InFrame (n*wSz))::armaAccesos xs rs (n+1)
                                           | armaAccesos (false::xs) (r::rs) n = (InReg r)::armaAccesos xs rs n
                                     in armaAccesos (true::f) argregs argsOffInicial end

fun maxRegFrame(f: frame) = !(#actualReg f)

(* Modificación, sugerencia Guillermo *)
fun allocArg (f: frame) b =  
  if b then
    let val acc = InFrame((!(#actualArg f) + argsOffInicial) * wSz)
        val _ = #ftAccesos f := acc :: !(#ftAccesos f)
        val _ = #actualArg f := !(#actualArg f)+1
    in acc end
  else  (* registro o stack *)
    if !(#actualReg(f)) > 0 then
      let val acc = InReg(tigertemp.newtemp())
          val _ = #ftAccesos f := acc :: !(#ftAccesos f)
          val _ = #actualReg f := !(#actualReg f)-1
      in acc end
    else (* vamos al stack *)
      let val acc = InFrame((!(#actualArg f) + argsOffInicial) * wSz)
          val _ = #ftAccesos f := acc :: !(#ftAccesos f)
          val _ = #actualArg f := !(#actualArg f)+1
      in acc end


fun allocLocal (f: frame) b =
    case b of
  true =>
  let val ret = InFrame(localsGap + (!(#actualLocal f)*wSz))
  in  #actualLocal f:=(!(#actualLocal f)-1); ret end
      | false => InReg(tigertemp.newtemp())


(* fun allocLocal (f:frame) b = *)
(*     if b then (* memoria *) *)
(*         InFrame (!(#actualLocal(f))*wSz) *)
(*         before #actualLocal(f) := !(#actualLocal(f))+localsDelta *)
(*     else InReg (newtemp()) *)

fun recorreArgs [] _ = []
  | recorreArgs _ [] = []
  | recorreArgs ((InReg t) :: xs) (reg::regs) = MOVE(TEMP t, TEMP reg) :: recorreArgs xs regs
  | recorreArgs ((InFrame a)::xs) regs = recorreArgs xs regs


fun exp(InFrame k) e = MEM(BINOP(PLUS, TEMP(fp), CONST k))
  | exp(InReg l) e = TEMP l

fun externalCall(s, l) = CALL(NAME s, l)

fun seq [] = EXP (CONST 0)
  | seq [s] = s
  | seq (x::xs) = SEQ (x, seq xs)

fun procEntryExit1 (fr: frame, body) = 
  let val (entry,exit) = List.foldl 
                          (fn (r,(ent,exi)) => let val nt = tigertemp.newtemp()
                                               in (MOVE (TEMP nt, TEMP r)::ent, MOVE (TEMP r, TEMP nt)::exi)
                                               end ) ([],[]) calleesaves
      val acomodaArgs = rev(recorreArgs (!(#ftAccesos fr)) argregs)
      val acomoda = acomodaArgs (*(MOVE (TEMP sp, (BINOP(MINUS,TEMP sp, MEM(NAME (#name fr^"_fs"))))))::acomodaArgs*)
  in seq(entry@acomoda@[body]@exit) end

(* fun procEntryExit2(frame,body) = *)
(*     body@(tigerassem.Oper{assem="",src[rv,rf,ff]@callee_saves,drt=[],jump=NONE}) *)

end
