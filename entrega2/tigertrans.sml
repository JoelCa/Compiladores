structure tigertrans :> tigertrans = struct

open tigerframe
open tigertree
open tigertemp
open tigerabs

exception breakexc
exception divCero
	  
type level = {parent:frame option , frame: frame, level: int} (*parent, es el frame de la función que la anida*)
type access = tigerframe.access

type frag = tigerframe.frag
val fraglist = ref ([]: frag list)

val actualLevel = ref ~1 (* _tigermain debe tener level = 0. *)
fun getActualLev() = !actualLevel

val outermost: level = {
    parent=NONE,
    frame=newFrame{name="_tigermain", formals=[]}, level=getActualLev()
}

fun newLevel{parent={parent, frame, level}, name, formals} = {
    parent=SOME frame,
    frame=newFrame{name=name, formals=formals},
    level=level+1}

fun getLevel{parent, frame, level} = level

fun allocArg{parent, frame, level} b = tigerframe.allocArg frame b
fun allocLocal{parent, frame, level} b = tigerframe.allocLocal frame b
fun formals{parent, frame, level} = tigerframe.formals frame

datatype exp =
	 Ex of tigertree.exp
       | Nx of tigertree.stm
       | Cx of label * label -> tigertree.stm

fun seq [] = EXP (CONST 0)
  | seq [s] = s
  | seq (x::xs) = SEQ (x, seq xs)

fun unEx (Ex e) = e
  | unEx (Nx s) = ESEQ(s, CONST 0)
  | unEx (Cx cf) =
    let
	val r = newtemp()
	val t = newlabel()
	val f = newlabel()
    in
	ESEQ(seq [MOVE(TEMP r, CONST 1),
		  cf (t, f),
		  LABEL f,
		  MOVE(TEMP r, CONST 0),
		  LABEL t],       
	     TEMP r)
    end

fun unNx (Ex e) = EXP e
  | unNx (Nx s) = s
  | unNx (Cx cf) =
    let
	val t = newlabel()
	val f = newlabel()
    in
	seq [cf(t,f),
	     LABEL t,
	     LABEL f]
    end

fun unCx (Nx s) = raise Fail ("Error (UnCx(Nx..))")
  | unCx (Cx cf) = cf
  | unCx (Ex (CONST 0)) =
    (fn (t,f) => JUMP(NAME f, [f]))
  | unCx (Ex (CONST _)) =
    (fn (t,f) => JUMP(NAME t, [t]))
  | unCx (Ex e) =
    (fn (t,f) => CJUMP(NE, e, CONST 0, t, f))

fun Ir(e) =
    let	fun aux(Ex e) = tigerit.tree(EXP e)
	  | aux(Nx s) = tigerit.tree(s)
	  | aux _ = raise Fail "bueno, a completar!"
	fun aux2(PROC{body, frame}) = aux(Nx body)
	  | aux2(STRING(l, "")) = l^":\n"
	  | aux2(STRING("", s)) = "\t"^s^"\n"
	  | aux2(STRING(l, s)) = l^":\t"^s^"\n"
	fun aux3 [] = ""
	  | aux3(h::t) = (aux2 h)^(aux3 t)
    in	aux3 e end

fun nombreFrame frame = print(".globl " ^ tigerframe.name frame ^ "\n")

(* While y for necesitan la última etiqueta para un break *)
(* Es distinto de lo que está en la carpeta*)
local
    val salidas: label option tigerpila.Pila = tigerpila.nuevaPila1 NONE
in
val pushSalida = tigerpila.pushPila salidas

fun popSalida() = tigerpila.popPila salidas

fun topSalida() =
    case tigerpila.topPila salidas of
	SOME l => l
      | NONE => raise Fail "break incorrecto!"			
end

val datosGlobs = ref ([]: frag list)
fun procEntryExit{level: level, body} =
    let	val label = STRING(name(#frame level), "")
	val body' = PROC{frame= #frame level, body=unNx body}
	val final = STRING(";;-------", "")
    in	datosGlobs:=(!datosGlobs@[label, body', final]) end

fun getResult() = !datosGlobs

fun stringLen s =
    let	fun aux [] = 0
	  | aux (#"\\":: #"x"::_::_::t) = 1+aux(t)
	  | aux (_::t) = 1+aux(t)
    in	aux(explode s) end

(* Equivale a  *)
(* STRINGlabel: *)
(*     .long 4 *)
(*     .string "hola" *)
fun stringExp(s: string) =
    let	val l = newlabel()
	val len = ".long "^makestring(stringLen s)
	val str = ".string \""^s^"\""
	val _ = datosGlobs:=(!datosGlobs @ [STRING(l, len), STRING("", str)])
    in	Ex(NAME l) end

fun preFunctionDec() =
    (pushSalida(NONE);
     actualLevel := !actualLevel+1)

fun functionDec(e, l, proc) =
    let	val body =
	    if proc then unNx e
	    else MOVE(TEMP rv, unEx e)
	val body' = procEntryExit1(#frame l, body)
	val () = procEntryExit{body=Nx body', level=l}
    in	Ex(CONST 0) end

fun postFunctionDec() =
    (popSalida(); actualLevel := !actualLevel-1)

fun unitExp() = Ex (CONST 0)

fun nilExp() = Ex (CONST 0)

fun intExp i = Ex (CONST i)

(*NOSOTROS*)
fun simpleVar(acc, nivel) =
    case acc of
        InFrame offset =>
        let fun aux 0 = TEMP fp
              | aux n = MEM (BINOP (PLUS, CONST fpPrevLev, aux(n-1)))
        in
            Ex (MEM(BINOP(PLUS,aux (!actualLevel - nivel), CONST offset)))
        end
      | InReg r => Ex (TEMP r)
                   
fun varDec(acc) = simpleVar(acc, getActualLev())

(* var es el código que "apunta" al inicio del arreglo, y field es un entero que indica
la posición del miembro, dado por el TRecord correspondiente *)
fun fieldVar(var, field) =
    (* NOSOTROS *) 
    let
	val a = unEx var
	val ra = newtemp()
    in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
                     EXP(externalCall("_checkNil", [TEMP ra]))  (*no retorna nada *)
                    ],
		 MEM(BINOP(PLUS, TEMP ra, BINOP(LSHIFT, CONST field, CONST tigerframe.log2WSz)))
                )
          )
    end

(* arr es el código que "apunta" al inicio del arreglo, e ind es el código
de una expresión entera, que indica la posición que se quiere indexar*)
fun subscriptVar(arr, ind) =
(*NOSOTROS*)
(*Originalmente usaba: "_checkindex"*)
    let
	val a = unEx arr
	val i = unEx ind
	val ra = newtemp()
	val ri = newtemp()
    in
	Ex( ESEQ(seq[MOVE(TEMP ra, a),
		     MOVE(TEMP ri, i),
		     EXP(externalCall("_checkIndexArray", [TEMP ra, TEMP ri])) (* no retorna nada *)
                    ],
                 MEM( BINOP(PLUS, TEMP ra,
                            case i of
                                CONST k => CONST (k*tigerframe.wSz)
                              | _ => BINOP(LSHIFT, i, CONST tigerframe.log2WSz)
                           )
                    )
                )
          )
    end

(* l: es una lista de tuplas (code, i), donde "code" es el cod. intermedio del
miembro en la posición i, del record*)
(* Obs: Se guarda en memória el resultado que se le quiere asignar a cada miembro, con el
orden dado por los indices del TRecord correspondiente *)
(* Duda: se estaría reservando espacio de mem., cada vez que se le asigna un nuevo valor
a un miembro del record? No. Cuando se tiene un recordExp, se define un nuevo record.*)
fun recordExp l =
    (* NOSOTROS *)
    let val ret = newtemp()
        fun genTemps 0 = []
          | genTemps n = newtemp() :: genTemps(n-1)
        val regs = genTemps (length l)
        fun aux ((e,s), t) = (MOVE (TEMP t, unEx e), s, TEMP t)
        val lexps = map aux (ListPair.zip(l, regs))
        val lexps' = map #1 lexps
        val l' = Listsort.sort (fn((_,m,_),(_,n,_)) => Int.compare (m,n)) lexps (*ordena la lista en orden no decreciente,
                                                                                  según la posición que ocupan en el TRecord*)
    in Ex (ESEQ (seq(lexps' @ [EXP (externalCall("_allocRecord", CONST(length l)::(List.map #3 l'))), (* allocRecord es una función de long. variable, que reserva espacio con un malloc,
                                                                                                         llena la i-ésima posición con el i-ésimo parámetro que recibe*)
                               MOVE(TEMP ret, TEMP rv)]), TEMP ret)) (*el registro rv, tiene lo que retorna el allocRecord? Si*)
    end

(*DUDA: por que no se guardan "s" e "i" en temporarios, para pasarlos a la función "_initArray"? No es necesario.*)
(*NOTA: la implementación de "_initArray" está mal*)
fun arrayExp{size, init} =
(* NOSOTROS *)
(*Originalmente usaba: "allocArray"*)
    let
	val s = unEx size
	val i = unEx init
    in
	Ex (externalCall("_initArray", [s, i])) (*retornaría el inicio del arreglo: i. En la posición i-1
                                                 se encuentra el tamaño que fue reservado*)
    end

(* external : indica si es una func. de libreria o no (booleano). *)
(*            Las funciónes de librerias no tienen static link *)
(* isproc : indica si devuelve algo (bool) *)
(* level : el nivel, un record *)
(* ls : la lista de argumentos  *)
fun callExp (name,external,isproc,lev:level,ls) = 
    let fun menAMay 0 = TEMP fp
          | menAMay n = MEM (BINOP (PLUS, menAMay(n-1), CONST fpPrevLev))
        val fplev = if (#level lev) = getActualLev() (* getActualLev, nos da el nivel de la función actual,
                                                        es decir el nivel de la llamante, en un callExp*)
                    then MEM (BINOP (PLUS, TEMP fp, CONST fpPrevLev))
                    else if (#level lev) > getActualLev()
                    then menAMay (getActualLev() - (#level lev) + 1)
                    else TEMP fp
        fun preparaArgs [] (rt,re) = (rt, re)
          | preparaArgs (h::t) (rt,re) =  (* rt son constantes,etc; re son expresiones a evaluar *)
            case h of
                Ex(CONST s) => preparaArgs t ((CONST s)::rt, re)
              | Ex(NAME s) => preparaArgs t ((NAME s)::rt, re)
              | Ex(TEMP s) => preparaArgs t ((TEMP s)::rt, re)
              |_ =>
               let
                   val t' = newtemp()
               in preparaArgs t ((TEMP t')::rt, (MOVE(TEMP t', unEx h))::re)
               end

        val (ta, ls') = preparaArgs (rev ls) ([],[]) (* aplica "rev ls", para que "ta" quede en el orden correcto *)
        val ta' = if external then ta else fplev::ta
    in
        if isproc
        then Nx (seq (ls'@[EXP(CALL(NAME name, ta'))]))
        else
            Ex (ESEQ (seq ls',
                      CALL(NAME name, ta')))
    end

fun letExp ([], body) = Ex (unEx body)
  |  letExp (inits, body) = Ex (ESEQ(seq inits,unEx body))

(*NOSOTROS*)
fun breakExp() = 
    let val ts = topSalida()
    in Nx (JUMP (NAME ts, [ts]))
    end

fun seqExp ([]:exp list) = Nx (EXP(CONST 0))
  | seqExp (exps:exp list) =
    let
	fun unx [e] = []
	  | unx (s::ss) = (unNx s)::(unx ss)
	  | unx[] = []
    in
	case List.last exps of
	    Nx s =>
	    let val unexps = map unNx exps
	    in Nx (seq unexps) end
	  | Ex e => Ex (ESEQ(seq(unx exps), e))
	  | cond => Ex (ESEQ(seq(unx exps), unEx cond))
    end

fun preWhileForExp() = pushSalida(SOME(newlabel()))

fun postWhileForExp() = (popSalida(); ())


(*NOSOTROS*)
fun forExp {lo, hi, var, body} =
    let
        val elo = unEx lo
        val ehi = unEx hi
        val evar = unEx var
        val ebody = unNx body
        val (l1,l2,l3) = (newlabel(),newlabel(),topSalida())
    in Nx (seq (case hi of (*hacemos esta diferenciación para tener una pequeña optimización *)
                    Ex(CONST n) =>
                    if valOf Int.maxInt = n then
                        [ MOVE (evar, elo),
                          LABEL l2,
                          CJUMP(LE, evar, CONST n, l1, l3),
                          LABEL l1,
                          ebody,
                          CJUMP(EQ, evar,CONST n, l3, l1), (*sin este jump, se quedaria bucleando infinitamente*)
                          LABEL l1,
                          MOVE(evar,BINOP(PLUS,evar,CONST 1)),
                          JUMP(NAME l2,[l2]),
                          LABEL l3
                        ]
                    else
                        [ MOVE (evar, elo),
                          LABEL l2,
                          CJUMP(LE, evar, CONST n, l1, l3),
                          LABEL l1,
                          ebody,
                          LABEL l1,
                          MOVE(evar,BINOP(PLUS,evar,CONST 1)),
                          JUMP(NAME l2,[l2]),
                          LABEL l3
                        ]   
                  | _ =>
                    let val t = newtemp() (*se crea una var. "fresca",
                                            pues el for tiene semántica de Fortran*)
                    in
                        [ MOVE (evar, elo),
                          MOVE(TEMP t, ehi),
                          CJUMP(LE, evar, TEMP t, l2, l3),
                          LABEL l2,
                          ebody,
                          CJUMP(EQ,evar,TEMP t, l3, l1),
                          LABEL l1,
                          MOVE(evar, BINOP(PLUS,evar,CONST 1)),
                          JUMP(NAME l2, [l2]),
                          LABEL l3
                        ]
                    end     
          ))
    end


fun whileExp {test: exp, body: exp, lev:level} =
    (* NOSOTROS *)
    let
	val cf = unCx test
	val expb = unNx body
	val (l1, l2, l3) = (newlabel(), newlabel(), topSalida())
    in
	Nx (seq[LABEL l1,
		cf(l2,l3),
		LABEL l2,
		expb,
		JUMP(NAME l1, [l1]),
		LABEL l3])
    end

fun ifThenExp{test, then'} =
    (* NOSOTROS *)
    let val e1 = unCx test
        val e2 = unNx then'
        val (t,f) = (newlabel(), newlabel())
    in
        Nx (seq [e1 (t,f),
                 LABEL t,
                 e2,
                 LABEL f])
    end

fun ifThenElseExp {test,then',else'} =
    (* NOSOTROS *)
    let val e1 = unCx test
        val e2 = unEx then'
        val e3 = unEx else'
        val (t, f, r, e) = (newlabel(), newlabel(), newtemp(), newlabel())
    in
        Ex (ESEQ (seq [e1 (t, f),
                       LABEL t,
	               MOVE(TEMP r, e2),
                       JUMP (NAME e,[e]),
                       LABEL f,
                       MOVE(TEMP r, e3),
                       LABEL e],
                  TEMP r))
    end
        
       
fun ifThenElseExpUnit {test,then',else'} =
    (* NOSOTROS *)
    let val e1 = unCx test
        val e2 = unNx then'
        val e3 = unNx else'
        val (t,f,e) = (newlabel(), newlabel(), newlabel())
    in
        Nx (seq [e1 (t,f),
                 LABEL t,
                 e2,
                 JUMP (NAME e, [e]),
                 LABEL f,
                 e3,
                 LABEL e])
    end

fun assignExp{var, exp} =
    let
	val v = unEx var
	val vl = unEx exp
    in
	Nx (MOVE(v,vl))
    end

fun binOpIntExp {left, oper, right} = 
    (* NOSOTROS *)
    let val l = unEx left
        val r = unEx right
    in
        case oper of
            PlusOp => Ex (BINOP (PLUS,l,r))
          | MinusOp => Ex (BINOP (MINUS,l,r))
          | TimesOp => Ex (BINOP (MUL,l,r))
          | DivideOp => Ex (BINOP (DIV,l,r))
          | _ => raise Fail ("Error: se esperaba operador algebraico")
    end

fun binOpIntRelExp {left,oper,right} =
    (* NOSOTROS *)
    let val l = unEx left
        val r = unEx right
        fun opint oper = fn (t,f) => CJUMP(oper, l, r, t, f)
    in
        case oper of
            EqOp => Cx (opint EQ)
          | NeqOp => Cx (opint NE)
          | LtOp => Cx (opint LT)
          | LeOp => Cx (opint LE)
          | GtOp => Cx (opint GT)
          | GeOp => Cx (opint GE)
          | _ => raise Fail ("Error: se esperaba operador de comparacion") 
    end

fun binOpStrExp {left,oper,right} =
    (* NOSOTROS *)
    let val l = unEx left
        val r = unEx right
        fun subst oper = fn (t,f) => CJUMP(oper, ESEQ(EXP(externalCall ("_stringCompare",[l,r])), TEMP rv), CONST 0, t, f)
    in
        case oper of
            EqOp => Cx (subst EQ)
          | NeqOp => Cx (subst NE)
          | LtOp => Cx (subst LT)
          | LeOp => Cx (subst LE)
          | GtOp => Cx (subst GT)
          | GeOp => Cx (subst GE)
          | _ => raise Fail ("Error: se esperaba operador de comparación de strings") 
    end
end
