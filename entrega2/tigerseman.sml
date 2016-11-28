structure tigerseman :> tigerseman =
struct

(*Operaciones básicas copiadas de la carpeta*)
infix -- ---
infix rs ls

fun x ls f = fn y => f(x,y)
fun f rs y = fn x => f(x,y)
fun l -- e = List.filter (op <> rs e) l
fun fst (x, _) = x and snd (_, y) = y
fun lp --- e = List.filter ((op <> rs e) o fst) lp

fun printRef v = "\"" ^ v ^ "\""


open tigerabs
open tigersres
open tigertrans
open tigerpp
open tigerit
         
type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
tabNueva(),
[("int", TInt), ("string", TString)])

val levelPila: tigertrans.level tigerpila.Pila = tigerpila.nuevaPila1(tigertrans.outermost) 
fun pushLevel l = tigerpila.pushPila levelPila l
fun popLevel() = tigerpila.popPila levelPila 
fun topLevel() = tigerpila.topPila levelPila

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
tabNueva(),
[("print", Func{level=topLevel(), label="print",
		formals=[TString], result=TUnit, extern=true}),
 ("flush", Func{level=topLevel(), label="flush",
		formals=[], result=TUnit, extern=true}),
 ("getchar", Func{level=topLevel(), label="getstr",
		  formals=[], result=TString, extern=true}),
 ("ord", Func{level=topLevel(), label="ord",
	      formals=[TString], result=TInt, extern=true}),
 ("chr", Func{level=topLevel(), label="chr",
	      formals=[TInt], result=TString, extern=true}),
 ("size", Func{level=topLevel(), label="size",
	       formals=[TString], result=TInt, extern=true}),
 ("substring", Func{level=topLevel(), label="substring",
		    formals=[TString, TInt, TInt], result=TString, extern=true}),
 ("concat", Func{level=topLevel(), label="concat",
		 formals=[TString, TString], result=TString, extern=true}),
 ("not", Func{level=topLevel(), label="not",
	      formals=[TInt], result=TInt, extern=true}),
 ("exit", Func{level=topLevel(), label="exit",
	       formals=[TInt], result=TUnit, extern=true})
])

fun tipoReal (TTipo (s, ref (SOME (t)))) = tipoReal t
  | tipoReal t = t

fun tiposIguales (TRecord _) TNil = true
  | tiposIguales TNil (TRecord _) = true 
  | tiposIguales (TRecord (_, u1)) (TRecord (_, u2 )) = (u1=u2)
  | tiposIguales (TArray (_, u1)) (TArray (_, u2)) = (u1=u2)
  | tiposIguales (TTipo (_, r)) b =
    let
	val a = case !r of
		    SOME t => t
		  | NONE => raise Fail "No debería pasar! (1)"
    in
	tiposIguales a b
    end
  | tiposIguales a (TTipo (_, r)) =
    let
	val b = case !r of
		    SOME t => t
		  | NONE => raise Fail "No debería pasar! (2)"
    in
	tiposIguales a b
    end
  | tiposIguales a b = (a=b)

fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
	fun trexp(VarExp v) = trvar(v)
	  | trexp(UnitExp _) = {exp=unitExp(), ty=TUnit}
	  | trexp(NilExp _)= {exp=nilExp(), ty=TNil}
	  | trexp(IntExp(i, _)) = {exp=intExp i, ty=TInt}
	  | trexp(StringExp(s, _)) = {exp=stringExp(s), ty=TString}
	  | trexp(CallExp({func = f, args = xs}, nl)) =
            (* NOSOTROS *)
	    let
		val {formals = argsType, result = resultType, label = name, level = level, extern = extern} =
		    case tabBusca(f,venv) of
			SOME (Func e) => e
		      | _ => error(printRef f ^ " no está declarada", nl)

		fun compararListaTipos [] [] argsCode = (true, argsCode)
		  | compararListaTipos _ [] _ = error(printRef f ^ " tiene muchos argumentos", nl)
		  | compararListaTipos [] _  _= error(printRef f ^ " tiene pocos argumentos", nl)
		  | compararListaTipos (x::xs) (y::ys) argsCode =
                    let val {ty = expType, exp = expCode} = trexp x
                    in
		        if tiposIguales expType y then
                            let val (b,ac) = compararListaTipos xs ys argsCode
                            in (b, expCode::ac)
                            end
		        else
                            (false, [])
                    end
                val isProc = case resultType of
                                  TNil => true
                                | _ => false
                val (valid, argsCode) = compararListaTipos xs argsType []
	    in
		if valid then
                    {exp = callExp(name,extern,isProc,level,argsCode), ty = resultType}
		else
		    error(printRef f ^ " es llamada con argumento/s inválido/s", nl)
	    end
	  | trexp(OpExp({left, oper=EqOp, right}, nl)) =
	    let
		val {exp=explCode, ty=tyl} = trexp left
		val {exp=exprCode, ty=tyr} = trexp right
                val _ = (printTab (venv); print("\n"))
                val _ = print("izquierda "^(showT tyl)^" - derecha "^(showT tyr)^"\n")
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
		    {exp=if tiposIguales tyl TString then binOpStrExp {left=explCode,oper=EqOp,right=exprCode} else binOpIntRelExp {left=explCode,oper=EqOp,right=exprCode}, ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
	    let
		val {exp=explCode, ty=tyl} = trexp left
		val {exp=exprCode, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
		    {exp=if tiposIguales tyl TString then binOpStrExp {left=explCode,oper=NeqOp,right=exprCode} else binOpIntRelExp {left=explCode,oper=NeqOp,right=exprCode}, ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper, right}, nl)) = 
	    let
		val {exp=explCode, ty=tyl} = trexp left
		val {exp=exprCode, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr then
		    case oper of
			PlusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=explCode, oper=oper, right=exprCode},ty=TInt} else error("Error de tipos", nl)
		      | MinusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=explCode, oper=oper, right=exprCode},ty=TInt} else error("Error de tipos", nl)
		      | TimesOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=explCode, oper=oper, right=exprCode},ty=TInt} else error("Error de tipos", nl)
		      | DivideOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=explCode, oper=oper, right=exprCode},ty=TInt} else error("Error de tipos", nl)
		      | LtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=explCode,oper=oper,right=exprCode} else binOpStrExp {left=explCode,oper=oper,right=exprCode},ty=TInt} 
				else error("Error de tipos", nl)
		      | LeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then 
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=explCode,oper=oper,right=exprCode} else binOpStrExp {left=explCode,oper=oper,right=exprCode},ty=TInt} 
				else error("Error de tipos", nl)
		      | GtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=explCode,oper=oper,right=exprCode} else binOpStrExp {left=explCode,oper=oper,right=exprCode},ty=TInt} 
				else error("Error de tipos", nl)
		      | GeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=explCode,oper=oper,right=exprCode} else binOpStrExp {left=explCode,oper=oper,right=exprCode},ty=TInt} 
				else error("Error de tipos", nl)
		      | _ => raise Fail "No debería pasar! (3)"
		else error("Error de tipos", nl)
	    end
	  | trexp(RecordExp({fields, typ}, nl)) =
	    (* NOSOTROS *)
            let
		val (tr, tn) = case tabBusca(typ, tenv) of
				   SOME t => (case tipoReal t of
						  TRecord (cs, u) => (cs, u)
						| _ => error(printRef typ^" no es de tipo record", nl))
				 | NONE => error("Tipo inexistente ("^typ^")", nl)
                fun checkFields [] r = r
                  | checkFields ((s,e)::flds) r =
                    let val (t',i') = (case List.find (fn x => #1 x = s) tr of
                                           SOME s => (#2 s, #3 s)
                                         | NONE => error (printRef s ^ " campo inexistente", nl))
                        val {exp = expCode, ty = te'} = trexp e
                        val _ = if not (tiposIguales te' t') then error ("Tipos no coinciden en record", nl) else ()
                    in checkFields flds ((expCode,i')::r) end
                val r' = checkFields fields []
            in
                {exp = recordExp(rev r'), ty = TRecord (tr, tn)} (* Por que hace rev r'? el orden importa? *)
            end
	  | trexp(SeqExp(s, nl)) =
	    let	val lexti = map trexp s
		val exprs = map (fn{exp, ty} => exp) lexti
		val {exp, ty=tipo} = hd(rev lexti)
	    in	{ exp=seqExp (exprs), ty=tipo } end
	  | trexp(AssignExp({var = SimpleVar s, exp = e}, nl)) =
	    (*NOSOTROS*)
            let
                val {ty = expType, exp = expCode} = trexp e
                val {ty = varType, exp = varCode} = trvar ((SimpleVar s),nl)
            in
                case tabBusca(s, venv) of
                    SOME (IntReadOnly _) => error(printRef s ^ " es de solo lectura",nl) (*ARREGLAR*)
                  | SOME (Var {ty=tyVar,access=acc,level=level}) => 
                    if (tiposIguales expType varType) andalso (tiposIguales tyVar varType) then
                        {exp=assignExp{var=varCode,exp=expCode}, ty = TUnit }
                    else
                        error("tipos incompatibles en asignación", nl)
                  | _ =>
                    error("asignación inválida", nl)
            end
            (* La traducción de SimpleVar a una expresión del tree, consiste en buscar su access, *)
            (* y pasarla a: MEM(BINOP(suma,TEMP del FP,CONST del offset)) *)
	  | trexp(AssignExp ({var, exp}, nl)) =
	    (*NOSOTROS*)
            let
                val {ty = expType, exp = expCode} = trexp exp
                val {ty = varType, exp = varCode} = trvar (var,nl)
            in
                if tiposIguales expType varType then
                    {exp=assignExp{var=varCode,exp=expCode}, ty = TUnit }
                else
                    error("tipos incompatibles en asignación", nl)
            end

	  | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
	    let val {exp=testexp, ty=tytest} = trexp test
		val {exp=thenexp, ty=tythen} = trexp then'
		val {exp=elseexp, ty=tyelse} = trexp else'
	    in
		if tipoReal tytest=TInt andalso tiposIguales tythen tyelse then
		    {exp=if tipoReal tythen=TUnit then ifThenElseExpUnit {test=testexp,then'=thenexp,else'=elseexp} else ifThenElseExp {test=testexp,then'=thenexp,else'=elseexp}, ty=tythen}
		else error("Error de tipos en if" ,nl)
	    end
	  | trexp(IfExp({test, then', else'=NONE}, nl)) =
	    let val {exp=exptest,ty=tytest} = trexp test
		val {exp=expthen,ty=tythen} = trexp then'
	    in
		if tipoReal tytest=TInt andalso tythen=TUnit then
		    {exp=ifThenExp{test=exptest, then'=expthen}, ty=TUnit}
		else error("Error de tipos en if", nl)
	    end
	  | trexp(WhileExp({test, body}, nl)) =
	    (* NOSOTROS *)
            let
		val ttest = trexp test
                val _ = preWhileForExp()
		val tbody = trexp body
                val expWhile = whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()}
                val _ = postWhileForExp()
	    in
		if tipoReal (#ty ttest) = TInt andalso #ty tbody = TUnit then {exp=expWhile, ty=TUnit}
		else if tipoReal (#ty ttest) <> TInt then error("Error de tipo en la condición", nl)
		else error("El cuerpo de un while no puede devolver un valor", nl)
	    end
          | trexp(ForExp({var, escape, lo, hi, body}, nl)) =
            (* NOSOTROS *)
            let
                val {exp=explo, ty=tylo} = trexp lo
                val {exp=exphi, ty=tyhi} = trexp hi
                val acc' = allocLocal (topLevel()) (!escape) (*aloja una variable, en el frame actual*)
                val level = getActualLev()
                val _ = if tiposIguales tylo TInt andalso tiposIguales tyhi TInt then ()
                        else error("for: Cotas no enteras", nl)
                val _ = preWhileForExp()
                val venv' = tabRInserta(var,IntReadOnly {access=acc', level=level}, venv) (* genera tabla nueva *)
                val {exp=ebody, ty=tybody} = transExp (venv', tenv) body
                val _ = if tiposIguales tybody TUnit then ()
                        else error("for: Cuerpo retorna valor", nl)
                val evar = simpleVar(acc', 0)
                val efor = forExp {lo=explo,  hi=exphi, var=evar, body=ebody}
                val _ = postWhileForExp()
            in
                {exp=efor, ty=tybody}
            end
	  | trexp(LetExp({decs, body}, _)) =
	    let
		fun aux (d, (v, t, exps1)) =
		    let
			val (v', t', exps2) = trdec (v, t) d
		    in
			(v', t', exps1@exps2)
		    end
		val (venv', tenv', expdecs) = List.foldl aux (venv, tenv, []) decs
		val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
	    in 
		{exp=seqExp(expdecs@[expbody]), ty=tybody}
	    end
	  | trexp(BreakExp nl) =
            (*NOSOTROS*)
	    ({exp=breakExp(), ty=TUnit}
	     handle Empty => error("break: fuera de while/for", nl))
	  | trexp(ArrayExp({typ, size = e1, init = e2}, nl)) =
            (*NOSOTROS*)
            let
                val {ty = typeSize, exp = sizeCode} = trexp e1
                val {ty = typeInit, exp = initCode} = trexp e2
                val (t,u) = (case tabBusca (typ,tenv) of
                                 SOME (TArray (t,u)) => (t,u)
                               | SOME tt => error(printRef typ ^ " no es de tipo array",nl)
                               | NONE => error(printRef typ ^ " no es un tipo",nl))
                val _ = if(not(tiposIguales typeSize TInt)) then
                            error(printRef typ ^ " tiene un tamaño inválido",nl)
                        else
                            if(not(tiposIguales typeInit t)) then
                                error(printRef typ ^ " es inicializado incorrectamente",nl)
                            else ()
            in
                {exp = arrayExp{size = sizeCode, init = initCode}, ty = TArray(typeInit,u)}
            end
	and trvar(SimpleVar s, nl) =
            (* NOSOTROS *)
            let
		val (varType,access,level) =
		    case tabBusca (s, venv) of
			SOME (Var {ty = t, access=access, level=level}) => (t,access,level)
                      | SOME (IntReadOnly {access=access, level=level}) => (TInt,access,level)
                      | SOME _ => error (printRef s ^ " es de tipo inválido", nl)
		      | NONE => error(printRef s ^ " no fue declarada", nl)
                val _ = print("tipo :"^(showT varType)^"\n")
            in
		{exp=simpleVar(access, level), ty=varType}
            end
	  | trvar(FieldVar(v, s), nl) =
            (* NOSOTROS *)
            let
                val {ty = typeVar, exp = varCode} = trvar (v,nl)
            in
                (case tipoReal typeVar of
                     TRecord (xs,_) =>
                     (case List.find(fn (nameMember,_,_) => nameMember = s) xs of
                          SOME (_,t,i) => {exp = fieldVar(varCode, i), ty = t}
                        | NONE => error("miembro " ^ printRef s ^" inexistente en el record",nl))
                   | _ => error("se intenta acceder a algo que no es un record",nl))
            end
          | trvar(SubscriptVar(v, e), nl) =
	    (*NOSOTROS*)
            let
                val {ty = typeExp, exp = expCode} = trexp e
                val {ty = typeVar, exp = varCode} = trvar (v,nl)
            in
                if (not(tiposIguales typeExp TInt)) then
                    error("La expresion no es de tip" ^ printRef "int",nl)
                else
                    case tipoReal typeVar of
                        TArray (t,_) => {exp = subscriptVar(varCode,expCode), ty = t}
                      | _ => error("se intenta acceder a algo que no es un arreglo",nl)
                
            end
        and trdec (venv, tenv) (VarDec ({name,escape = esc,typ=NONE,init},pos)) = 
	    (*NOSOTROS*)
            let
                val {ty = typeExp, exp = initCode} = transExp (venv, tenv) init
                val (acc,level) = (allocLocal (topLevel()) (!esc), getActualLev())
                val venv' = case typeExp of
                                TNil => error (printRef name ^ " no es posible inferir su tipo", pos)
                              | _ => tabRInserta(name,Var {ty=typeExp,access=acc,level=level},venv)
            in
                (venv',tenv,[assignExp{var = simpleVar(acc,level), exp = initCode}]) (* Utiliza una lista por comodidad, es util por la lista vacia [], en FunctionDec, y TypeDec *)
            end
	  | trdec (venv,tenv) (VarDec ({name,escape = esc,typ=SOME s,init},pos)) =
            let
                val {ty = typeExp, exp = initCode} = transExp (venv, tenv) init
                val (acc,level) = (allocLocal (topLevel()) (!esc), getActualLev())
                val typeVar = (case tabBusca (s,tenv) of
                                   SOME t => t
                                 | NONE => error ("el tipo "^printRef s^" no está definido", pos))
            in
                if (not(tiposIguales typeExp typeVar)) then
                    error(printRef name ^ " con tipo incompatible",pos)
                else
                    let
                        val venv' = tabRInserta(name,Var {ty=typeVar,access=acc,level=level},venv)
                    in
                        (venv',tenv,[assignExp{var = simpleVar(acc,level), exp = initCode}])
                    end
            end
	  | trdec (venv,tenv) (FunctionDec fs) =
            (*NOSOTROS*)
            let 
                fun checkNames [] = (~1, "")
                  | checkNames (( {name=n,...} , nl)::xs) =
                    let 
                        val res = List.all (fn ({name=m,...},_) => m <> n) xs
                    in
                        if res then
                            checkNames xs
                        else
                            (nl, n)
                    end

                val (nl,name) = checkNames fs
                val _ = if (nl <> ~1) then error("declaración múltiple de la función " ^ printRef name,nl) else ()
                 
                (* esta funcion toma un record de la forma {name: symbol, escape: bool ref, typ: ty} y devuelve un elemento de tipo Tipo*)
                fun genTipo {name = s, typ = t, escape = esc} =
                    let val tTipo = (case t of
                                         NameTy n => (case tabBusca (n,tenv) of
                                                          NONE => raise Fail (printRef s ^ " tiene un tipo inexistente")
                                                        | SOME ttipo => ttipo)
                                       | _ => raise Fail (printRef s ^ " tiene un tipo incorrecto"))
                    in (s, tTipo, !esc) end

                fun putVars ([], _, env) = env  
                  | putVars ((s,vtype,esc)::xs, level, env) =
                    let val (acc, numLevel) = (allocArg level esc, getLevel level)
                    in
                        tabRInserta(s, Var {ty = vtype, access = acc, level = numLevel}, putVars (xs, level, env))
                    end

                fun putFuncs ([], env) = env  
                  | putFuncs ((((s,ftype),_)::xs), env) = tabRInserta(s, ftype, putFuncs (xs,env))

                (* esta funcion la utilizaremos para agregar cada una de las funciones de fs a venv *)
                fun genEnvEntry ({name = s, params = ps, result = NONE, body = exp}, pos) =
                    let val fmlPairs = map genTipo ps   
                        val fmls = map (#2) fmlPairs
                        val level = newLevel{parent=topLevel(), name = tigertemp.newlabel()^s, formals = map (#3) fmlPairs}
                        val f = Func {level = level, label = tigertemp.newlabel()^s, formals = fmls, result = TUnit, extern = false}
                    in
                        ((s,f),(fmlPairs,NONE))
                    end
                  | genEnvEntry ({name = s, params = ps, result = (SOME n), body = exp}, pos) =
                    let
                        val ttipo = (case tabBusca (n,tenv) of
                                         NONE => error(printRef n ^ " tiene un tipo de retorno inexistente", pos)
                                       | SOME t => t)
                        val fmlPairs = map genTipo ps
                        val fmls = map (#2) fmlPairs
                        val level = newLevel{parent=topLevel(), name = tigertemp.newlabel()^s, formals = map (#3) fmlPairs}
                        val f = Func {level = level, label = tigertemp.newlabel()^s, formals = fmls, result = ttipo, extern = false}
                    in
                        ((s,f),(fmlPairs,SOME ttipo))
                    end

                fun checkBodies _ [] [] = ()
                  | checkBodies venv (((_,fEntry:EnvEntry),(x,NONE))::xs) (({name = s, result = NONE, body = exp, ...}, pos)::fs) =
                    let val level = case fEntry of
                                        Func {level = level, ...} => level
                                      | _ => raise Fail "error interno: declaración de función"
                        val venv' = putVars (x, level, venv)
                        val _ = preFunctionDec()
                        val _ = pushLevel level
                        val {ty = tBody, exp = bodyCode} = transExp (venv',tenv) exp
                        val _ = functionDec (bodyCode, level, true)
                        val _ = popLevel()
                        val _ = postFunctionDec()
                    in
                        if not(tiposIguales TUnit tBody) then
                            error(printRef s ^ " tiene un tipo de retorno inválido", pos)
                        else
                            checkBodies venv xs fs
                    end
                  | checkBodies venv (((_,fEntry),(x, SOME ttipo))::xs) (({name = s, result = (SOME n), body = exp, ...}, pos)::fs) =
                    let
                        (* val ttipo = (case tabBusca (n,tenv) of *)
                        (*                 NONE => error(printRef n ^ " tiene un tipo de retorno inexistente", pos) *)
                        (*               | SOME t => t) *)
                        val level = case fEntry of
                                        Func {level = level, ...} => level
                                      | _ => raise Fail "error interno: declaración de función"
                        val venv' = putVars (x, level, venv)
                        val _ = preFunctionDec()
                        val _ = pushLevel level
                        val {ty = tBody, exp = bodyCode} = transExp (venv',tenv) exp
                        val _ = functionDec (bodyCode, level, false)
                        val _ = popLevel()
                        val _ = postFunctionDec()
                    in
                        if not(tiposIguales ttipo tBody) then
                            error(printRef s ^ " tiene un tipo de retorno inválido", pos)
                        else
                            checkBodies venv xs fs
                    end
                  | checkBodies _ _ _ = raise Fail "error interno: chequeo de tipos en función\n"
                                              

                val listFuncEntriesAndOthers = map genEnvEntry fs
                val venv' = putFuncs (listFuncEntriesAndOthers,venv)
                val _ = checkBodies venv' listFuncEntriesAndOthers fs
            in
                (venv', tenv, [])
            end
	  | trdec (venv,tenv) (TypeDec ts) =
            (*NOSOTROS*)
            let
                val firstNL = (#2(hd ts))

                fun checkNames [] = (~1, "")
                  | checkNames (( {name=n,...} , nl)::xs) =
                    let 
                        val res = List.all (fn ({name=m,...},_) => m <> n) xs
                    in
                        if res then
                            checkNames xs
                        else
                            (nl, n)
                    end

                val (nl,name) = checkNames ts
                val _ = if (nl <> ~1) then error("declaraciones múltiples del tipo " ^ printRef name,nl) else ()

                fun buscaArrRecords lt =
                    let fun buscaRecs [] recs = recs
                          | buscaRecs ((r as {name, ty = RecordTy _}) :: t) recs = buscaRecs t (r :: recs)
                          | buscaRecs ((r as {name, ty = ArrayTy _}) :: t) recs = buscaRecs t (r ::recs)
                          | buscaRecs (_ :: t) recs = buscaRecs t recs
                    in buscaRecs lt [] end

                fun genPares lt =
                    let
                        (* val lrecs = buscaArrRecords lt *)
                        fun genP [] res = res
                           |genP ({name, ty = NameTy s} :: t) res =
                            genP t ((s,name)::res)
                           |genP ({name, ty = ArrayTy s} :: t) res =
                            genP t ((s,name) :: res)
                           |genP ({name,ty = RecordTy lf} :: t) res =
                            let fun recorre ({typ = NameTy x, ...} :: t) =
                                    (case List.find ((op = rs x) o #name) lt  of (* cambié "lrecs" con "lt" *)
                                         SOME _ => recorre t
                                        |_ => x :: recorre t)
                                  | recorre (_ :: l) = recorre l
                                  | recorre [] = []
                                val res' = recorre lf
                                val res'' = List.map (fn x => (x,name)) res'
                            in genP t (res'' @ res) end
                    in
                        genP lt []
                    end

                (* Procesa la lista ordenada dada por el topsort, no procesa Arrays ni Records. Cree que NO es necesario
                usar "primeraPasada". *)
                fun primeraPasada [] decs recs env = env
                  | primeraPasada (sorted as (h::t)) decs recs env =
                    let
                        fun filt h {name, ty=NameTy t} = h = t
                          | filt h {name, ty=ArrayTy t} = h = t
                          | filt h {name, ty=RecordTy lt} = List.exists (fn {name, ...} => h = name) lt
                        val (ps,ps') = List.partition (filt h) decs
                        val ttopt = case List.find (fn {name,ty} => name = h) recs of
                                        SOME _ => NONE
                                      | NONE => (case tabBusca(h, env) of
                                                     SOME t => SOME t
                                                   | _ => NONE)
                        val env' = case ttopt of
                                       SOME tt => List.foldr (fn ({name, ty=NameTy _}, env) => tabRInserta(name, tt, env)
                                                             | (_, env) => env) env ps
                                     | _ => env
                    in primeraPasada t ps' recs env' end
                        
                (* Procesa records y arrays. Posiblemente, le da tipo a los
                NameTy que están definidos en base a records o arrays. *)
                fun segundaPasada batch env =
                    let
                        fun buscaEnv t =
                            case List.find (fn {name, ...} => name = t) batch of
                                SOME {name, ...} => TTipo(name, ref NONE)
                              | _ => case tabBusca(t, env) of
                                         SOME tt => tt
                                       | _ => error (printRef t^" es un tipo inexistente", firstNL)

                        fun precs [] env' = env'
                          | precs ({name, ty=RecordTy lf} :: t) env' =
                            let
                                val lf' = List.foldl (fn ({name, typ=NameTy t, ...}, l) => (name, buscaEnv t) :: l
                                                     | (_, l) => l) [] lf
                                val (_, lf'')= List.foldl (fn ((x,y),(n,l)) => (n+1, (x,y,n)::l)) (0,[]) lf'
                                val env'' = tabRInserta (name, TRecord (lf'', ref ()), env')
                            in precs t env'' end

                          | precs ({name, ty=ArrayTy ty} :: t) env' =
                            precs t (tabRInserta (name, TArray (buscaEnv ty, ref ()), env'))
                          
                          | precs ({name, ty = NameTy ty} :: t) env' = 
                            precs t (tabRInserta (name, buscaEnv ty, env'))

                    in precs batch env end
                        
                (* Reemplaza los tipos "punteros" a NONE, por punteros al record del cual
                son miembros y pone los tipos definitivos en los NameTy. *)
                fun fijaNONE [] env =
                    env
                  | fijaNONE ((name, TArray (TTipo (s, ref NONE), u)) :: t) env =
                    (case tabBusca(s, env) of
                         SOME r => fijaNONE t (tabRInserta (name, TArray (TTipo (s, ref (SOME r)), u) , env)) (* Antes estaba "SOME (r as (TRecord _)" *)
                       | _ => error (printRef s^" tipo inexistente", firstNL))
                  | fijaNONE ((name, TRecord (lf, u)) :: t) env =
                    let
                        fun busNONE ((s, TTipo (t, r), u), l) = 
                            (case !r of
                                 NONE => let val _ = r := SOME (tabSaca (t, env))
                                         in (s, TTipo (t,r), u) :: l end
                               | SOME e => (s, TTipo (t, r), u) :: l)
                          | busNONE (d, l) = d :: l
                        val lf' = List.foldl busNONE [] lf
                    in fijaNONE t (tabRInserta(name, TRecord (lf', u), env)) end
                  | fijaNONE ((name, TTipo (ty, _)) :: t) env =
                    let 
                        val (ta,env') = case tabBusca (ty,env) of
                                       SOME t => (t,tabRInserta (name, t, env))
                                     | NONE => raise Fail (printRef ty ^ " es un tipo no declarado")
                    in
                        fijaNONE t env'
                    end
                  | fijaNONE (_ :: t) env = fijaNONE t env
                                                   
                (* Fija tipos en un batch *)
                fun fijatipos batch env =
                    let
                        val pares = genPares batch

                        val _ = (print("Pares: "); map (fn (s, s') => print ("("^s^","^s'^")" ^ " - ")) pares ; print("\n"))

                        val ordered = topsort.topsort pares

                        val _ = (print("Tipos ordenados por el topsort: "); map (fn s => print (s ^ " - ")) ordered ; print("\n"))

                        val recs = buscaArrRecords batch
                        val env' = primeraPasada ordered batch recs env

                        val _ = (print("Tabla en el 1º procesa: ") ; printTab (env'); print("\n"))

                        val env'' = segundaPasada batch env'

                        val _ = (print("Tabla en el 2º procesa: ") ; printTab (env''); print("\n"))

                        val _ = map (fn (s,t) => print(s^" "^(showT t)^" - ")) (tabAList env'')

                        val _ = print("\n")

                        val env''' =  fijaNONE (tabAList env'') env''

                        val _ = map (fn (s,t) => print(s^" "^(showT t)^" - ")) (tabAList env''')

                        val _ = print("\n")
                    in env''' end
            in
                let
                    val tenv' = fijatipos (map (#1) ts) tenv
                in
                    (venv, tenv', [])
                end
            end
    in trexp end
fun transProg ex =
    let	val main =
	    LetExp({decs=[FunctionDec[({name="_tigermain", params=[],
					result=SOME "int", body=ex}, 0)]],
		    body=UnitExp 0}, 0)
	val _ = transExp(tab_vars, tab_tipos) main
        (*val _ = print (tigerit.tree (unNx exp))*)
    in	print "bien!\n" end
end
