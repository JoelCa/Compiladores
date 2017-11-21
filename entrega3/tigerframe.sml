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

    |    argn    |  fp+4*(n-1)
    |    ...     |
    |    arg5    |  fp+16
    |    arg4    |  fp+12
    --------------
    |   lr       |  fp+8
    |   ip       |  fp+4
    |   fp ant   |  fp
    |  fp level  |  fp-4   static link
    |   local1   |  fp-8
    |   local2   |  fp-12
    |   local3   |  fp-16
    |   local4   |  fp-20
    |   local5   |  fp-24
    |    ...     |
    |   localn   |  fp-4*(n+1)
    |  callee S1 |  fp-4*(n+2)
    |  callee S2 |  fp-4*(n+3)
    |    ...     |



*)
structure tigerframe :> tigerframe = struct

open tigertree

structure Table = Splaymap

type level = int

val fp             = "fp"         (* frame pointer:                            r11 *)
val ip             = "ip"         (* new-static base in inter-link-unit calls: r12 *)
val sp             = "sp"         (* stack pointer:                            r13 *)
val rv             = "r0"         (* return value                                  *)
val lr             = "lr"         (* link register:                            r14 *)
val pc             = "pc"         (* program counter:                          r15 *)
val wSz            = 4            (* word size in bytes                            *)
val log2WSz        = 2            (* base two logarithm of word size in bytes      *)
val fpPrev         = 0            (* offset (bytes)                                *)
val fpPrevLev      = ~4           (* offset (bytes)                                *)
val argsInicial    = 1             
val argsOffInicial = 2            (* words                                         *)
val argsGap        = wSz          (* bytes                                         *)
val localsInicial  = 0            (* words                                         *)
val localsGap      = ~8           (* bytes que indican el espacio entre el fp y el 1º local *)
val calldefs       = [rv]
val specialregs    = [rv, fp, sp, pc]
val argregs        = ["r0","r1","r2","r3"]
val callersaves    = []
val calleesaves    = ["r4","r5","r6","r7","r8","r9","r10"]
val allRegs        = argregs @ calleesaves @ [fp, ip, sp, lr, pc]

(* allRegs    = ["r0","r1","r2","r3","r4","r5","r6","r7","r8","r9","r10",ip,lr,fp,sp,pc] *)
(* asignables = ["r4","r5","r6","r7","r8","r9","r10"] *)

(*
  pc: En todo momento se está modificando
  sp: Apunta al tope del stack y en caso de modificarlo se está afectando la posición en la que se agregan cosas al stack
  fp: Apunta al frame actual y en caso de modificarlo no se estarían accediendo al frame correspondiente
*)

datatype access = InFrame of int | InReg of tigertemp.label

type frame = {
    name: string,
    formals: bool list,
    locals: bool list ref,
    actualArg: int ref,
    actualLocal: int ref,
    actualReg: int ref,
    ftAccesos : access list ref
}
type register = string
datatype frag = PROC of {body: tigertree.stm, frame: frame}
              | STRING of tigertemp.label * string

(* Agregamos un argumento escapado a la lista de formals, en representación del static link. *)
fun newFrame{name, formals} = {
    name        = name,
    formals     = true::formals,
    locals      = ref [],
    actualArg   = ref argsInicial,
    actualLocal = ref localsInicial,
    actualReg   = ref ((length argregs) - 1),           (* con la sugerencia de Guillermo *)
    ftAccesos   = ref [InFrame(fpPrevLev)]
}

fun name(f: frame) = #name f

fun string(l, s) = l^tigertemp.makeString(s)^"\n"

(* Los primeros 4 argumentos se guardarán en registro (incluido el static link). *)
(* Luego se pondrán en memoria, si son argumentos escapados. *)
fun formals({formals=f,...}:frame) = let fun armaAccesos [] _ _            = []
                                           | armaAccesos (_::xs) [] n      = (InFrame (n*wSz))::armaAccesos xs [] (n+1)
                                           | armaAccesos (_::xs) (r::rs) n = (InReg r)::armaAccesos xs rs n
                                     in armaAccesos f argregs argsOffInicial end

fun maxRegFrame(f: frame) = !(#actualReg f)


(* Modificación, sugerencia Guillermo *)
fun allocArg (f: frame) b =  
  if b then
    let val acc = InFrame((!(#actualArg f) + argsOffInicial) * wSz)
        val _ = #ftAccesos f := acc :: !(#ftAccesos f)
        val _ = #actualArg f := !(#actualArg f)+1
        val _ = #actualReg f := !(#actualReg f)-1
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
  let val _ =(#locals f) := b::(!(#locals f))
  in
    case b of
      true =>
        let val ret = InFrame(localsGap + (!(#actualLocal f)*wSz))
        in  #actualLocal f:=(!(#actualLocal f)-1); ret end
    | false => InReg(tigertemp.newtemp())
  end

fun exp(InFrame k) _ = MEM(BINOP(PLUS, TEMP(fp), CONST k))
  | exp(InReg l)   _ = TEMP l

fun recorreArgs [] _ = []
  | recorreArgs _ [] = []
  | recorreArgs (x::xs) (reg::regs) = MOVE(exp x (TEMP fp),TEMP reg) :: recorreArgs xs regs

fun externalCall(s, l) = CALL(NAME s, l)

fun seq [] = EXP (CONST 0)
  | seq [s] = s
  | seq (x::xs) = SEQ (x, seq xs)

fun procEntryExit1 (fr: frame, body) = 
  let val (entry,exit) = List.foldr
                          (fn (r,(ent,exi)) => let val nt = tigertemp.newtemp()
                                               in (MOVE (TEMP nt, TEMP r)::ent, MOVE (TEMP r, TEMP nt)::exi)
                                               end ) ([],[]) calleesaves
      val acomodaArgs = recorreArgs (rev (!(#ftAccesos fr))) argregs
      val a = [MOVE (TEMP fp, TEMP sp)]
      val acomoda =  acomodaArgs (*(MOVE (TEMP sp, (BINOP(MINUS,TEMP sp, MEM(NAME (#name fr^"_fs"))))))::acomodaArgs*)
  in seq(entry@acomoda@[body]@exit) end  (*seq(acomoda@[body]) end*) 

fun procEntryExit2(frame,body) = 
     body@[tigerassem.OPER {assem = "", src = [rv,sp]@calleesaves, dst = [], jump = NONE}]

fun procEntryExit3(fr: frame, body) =
  let
    (* space es el espacio que ocupan todos los locales, más el static link. *)
    val space = wSz * (List.foldr (fn (b, r) => if b then r+1 else r) 1 (!(#locals fr)))
  in
    { prolog = "push {fp,ip,lr}\nmov fp, sp\nsub sp, sp, #"^Int.toString space^"\n"
    , body = body
    , epilog = "mov sp, fp\npop {fp,ip,pc}\n"}
  end
end