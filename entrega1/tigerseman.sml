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

open tigerabs
open tigersres
open tigerpp

type expty = {exp: unit, ty: Tipo}

type venv = (string, EnvEntry) tigertab.Tabla
type tenv = (string, Tipo) tigertab.Tabla

val tab_tipos : (string, Tipo) Tabla = tabInserList(
tabNueva(),
[("int", TInt), ("string", TString)])

val tab_vars : (string, EnvEntry) Tabla = tabInserList(
tabNueva(),
[("print", Func{level=mainLevel, label="print",
		formals=[TString], result=TUnit, extern=true}),
 ("flush", Func{level=mainLevel, label="flush",
		formals=[], result=TUnit, extern=true}),
 ("getchar", Func{level=mainLevel, label="getstr",
		  formals=[], result=TString, extern=true}),
 ("ord", Func{level=mainLevel, label="ord",
	      formals=[TString], result=TInt, extern=true}),
 ("chr", Func{level=mainLevel, label="chr",
	      formals=[TInt], result=TString, extern=true}),
 ("size", Func{level=mainLevel, label="size",
	       formals=[TString], result=TInt, extern=true}),
 ("substring", Func{level=mainLevel, label="substring",
		    formals=[TString, TInt, TInt], result=TString, extern=true}),
 ("concat", Func{level=mainLevel, label="concat",
		 formals=[TString, TString], result=TString, extern=true}),
 ("not", Func{level=mainLevel, label="not",
	      formals=[TInt], result=TInt, extern=true}),
 ("exit", Func{level=mainLevel, label="exit",
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

fun printRef v = "\"" ^ v ^ "\""

fun transExp(venv, tenv) =
    let fun error(s, p) = raise Fail ("Error -- línea "^Int.toString(p)^": "^s^"\n")
	fun trexp(VarExp v) = trvar(v)
	  | trexp(UnitExp _) = {exp=(), ty=TUnit}
	  | trexp(NilExp _)= {exp=(), ty=TNil}
	  | trexp(IntExp(i, _)) = {exp=(), ty=TInt}
	  | trexp(StringExp(s, _)) = {exp=(), ty=TString}
	  | trexp(CallExp({func = f, args = xs}, nl)) =		
	    (* NOSOTROS *)		
	    let
		val {formals = argsType, result = resultType, ...} =
		    case tabBusca(f,venv) of
			SOME (Func e) => e
		      | _ => error(printRef f ^ " no está declarada", nl)

		fun compararListaTipos [] [] = true
		  | compararListaTipos _ [] = error(printRef f ^ " tiene muchos argumentos", nl)
		  | compararListaTipos [] _ = error(printRef f ^ " tiene pocos argumentos", nl)
		  | compararListaTipos (x::xs) (y::ys) =
                    let val {ty = expType, ...} = trexp x
                    in
		        if tiposIguales expType y then
                            compararListaTipos xs ys
		        else
                            false 
                    end
	    in
		if (compararListaTipos xs argsType) then
		    {exp=(), ty = resultType}
		else
		    error(printRef f ^ " es llamada con argumento/s inválido/s", nl)
	    end
	  | trexp(OpExp({left, oper=EqOp, right}, nl)) =
	    let
		val {exp=_, ty=tyl} = trexp left
		val {exp=_, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
	    let
		val {exp=_, ty=tyl} = trexp left
		val {exp=_, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then {exp=(), ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper, right}, nl)) = 
	    let
		val {exp=_, ty=tyl} = trexp left
		val {exp=_, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr then
		    case oper of
			PlusOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | MinusOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | TimesOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | DivideOp => if tipoReal tyl=TInt then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | LtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | LeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | GtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | GeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then {exp=(),ty=TInt} else error("Error de tipos", nl)
		      | _ => raise Fail "No debería pasar! (3)"
		else error("Error de tipos", nl)
	    end
	  | trexp(RecordExp({fields, typ}, nl)) =
            (*Reescrito de la carpeta*)
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
                        val {exp = e', ty = te'} = trexp e
                        val _ = if not (tiposIguales te' t') then error ("Tipos no coinciden en record", nl) else ()
                    in checkFields flds ((e',i')::r) end
                val r' = checkFields fields []
            in
                {exp = (), ty = TRecord (tr, tn)}
            end
	  | trexp(SeqExp(s, nl)) =
	    let	val lexti = map trexp s
		val exprs = map (fn{exp, ty} => exp) lexti
		val {exp, ty=tipo} = hd(rev lexti)
	    in	{ exp=(), ty=tipo } end
	  | trexp(AssignExp({var = SimpleVar s, exp = e}, nl)) =
	    (*NOSOTROS*)
            let
                val {ty = expType, ...} = trexp e
                val {ty = varType, ...} = trvar ((SimpleVar s),nl)
            in
                case tabBusca(s, venv) of
                    SOME IntReadOnly => error(printRef s ^ " es de solo lectura",nl)
                  | _ => 
                    if tiposIguales expType varType then
                        {exp=(), ty = TUnit }
                    else
                        error("tipos incompatibles en asignación", nl)
            end
	  | trexp(AssignExp ({var, exp}, nl)) =
	    (*NOSOTROS*)
            let
                val {ty = expType, ...} = trexp exp
                val {ty = varType, ...} = trvar (var,nl)
            in
                if tiposIguales expType varType then
                    {exp=(), ty = TUnit }
                else
                    error("tipos incompatibles en asignación", nl)
            end
	  | trexp(IfExp({test, then', else'=SOME else'}, nl)) =
	    let val {exp=testexp, ty=tytest} = trexp test
		val {exp=thenexp, ty=tythen} = trexp then'
		val {exp=elseexp, ty=tyelse} = trexp else'
	    in
		if tipoReal tytest=TInt andalso tiposIguales tythen tyelse then {exp=(), ty=tythen}
		else error("Tipos distintos en if" ,nl)
	    end
	  | trexp(IfExp({test, then', else'=NONE}, nl)) =
	    let val {exp=exptest,ty=tytest} = trexp test
		val {exp=expthen,ty=tythen} = trexp then'
	    in
		if tipoReal tytest=TInt andalso tythen=TUnit then {exp=(), ty=TUnit}
		else error("Tipo inválido en if", nl)
	    end
	  | trexp(WhileExp({test, body}, nl)) =
	    let
		val ttest = trexp test
		val tbody = trexp body
	    in
		if tipoReal (#ty ttest) = TInt andalso #ty tbody = TUnit then {exp=(), ty=TUnit}
		else if tipoReal (#ty ttest) <> TInt then error("Error de tipo en la condición", nl)
		else error("El cuerpo de un while no puede devolver un valor", nl)
	    end
	  | trexp(ForExp({var, lo = e1, hi = e2, body = e3, ...}, nl)) =
	    (* NOSOTROS *)
            let
                val {ty = typeLo, ...} = trexp e1
                val {ty = typeHi, ...} = trexp e2
                val venv' = tabRInserta (var,IntReadOnly,venv)
                val {ty = typeBody, ...} = transExp (venv', tenv) e3
            in
                if(not((tiposIguales typeLo typeHi) andalso (tiposIguales TInt typeLo)))
                then error("expresión/es con tipo/s inválido/s, en el for",nl)
                else
                    if(not(tiposIguales typeBody TUnit))
                    then error("el cuerpo del bucle tiene tipo inválido",nl)
                    else
                        {exp = (), ty = TUnit}
            end
	  | trexp(LetExp({decs, body}, _)) =
	    let
		val (venv', tenv', _) = List.foldl (fn (d, (v, t, _)) => trdec(v, t) d) (venv, tenv, []) decs
		val {exp=expbody,ty=tybody}=transExp (venv', tenv') body
	    in 
		{exp=(), ty=tybody}
	    end
	  | trexp(BreakExp nl) =
            (*NOSOTROS*)
            (* Ignoramos los breaks mal puestos*)
	    {exp=(), ty=TUnit}
	  | trexp(ArrayExp({typ, size = e1, init = e2}, nl)) =
            (*NOSOTROS*)
            let
                val {ty = typeSize, ...} = trexp e1
                val {ty = typeInit, ...} = trexp e2
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
                {exp = (), ty = TArray(typeInit,u)}
            end
	and trvar(SimpleVar s, nl) =
            (* NOSOTROS *)
            let
		val varType =
		    case tabBusca (s, venv) of
			SOME (Var {ty = t}) => t
                      | SOME (IntReadOnly) => TInt
                      | SOME _ => error (printRef s ^ " es de tipo inválido", nl)
		      | NONE => error(printRef s ^ " no fue declarada", nl)
            in
		{exp=(), ty=varType}
            end
	  | trvar(FieldVar(v, s), nl) =
            (*NOSOTROS*)
            let
                val {ty = typeVar, ...} = trvar (v,nl)
            in
                (case tipoReal typeVar of
                     TRecord (xs,_) =>
                     (case List.find(fn (nameMember,_,_) => nameMember = s) xs of
                          SOME (_,t,_) => {exp = (), ty = t}
                        | NONE => error("miembro " ^ printRef s ^" inexistente en el record",nl))
                   | _ => error("se intenta acceder a algo que no es un record",nl))
            end
	  | trvar(SubscriptVar(v, e), nl) =
	    (*NOSOTROS*)
            let
                val {ty = typeExp, ...} = trexp e
                val {ty = typeVar, ...} = trvar (v,nl)
            in
                if (not(tiposIguales typeExp TInt)) then
                    error("La expresion no es de tip" ^ printRef "int",nl)
                else
                    case tipoReal typeVar of (*Agregé "tipoReal", para que funcione el test42.tig*)
                        TArray (t,_) => {exp = (), ty = t}
                      | _ => error("se intenta acceder a algo que no es un arreglo",nl)
                
            end
        and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
	    (*NOSOTROS*)
            let
                val {ty = typeExp, ...} = transExp (venv, tenv) init
                val venv' = case typeExp of
                                TNil => error (printRef name ^ " no es posible inferir su tipo", pos)
                              | _ => tabRInserta(name,Var {ty=typeExp},venv)
            in
                (venv',tenv,[]) 
            end
	  | trdec (venv,tenv) (VarDec ({name,escape,typ=SOME s,init},pos)) =
            let
                val {ty = typeExp, ...} = transExp (venv, tenv) init
                val typeVar = (case tabBusca (s,tenv) of
                                   SOME t => t
                                 | NONE => error ("el tipo "^printRef s^" no está definido", pos))
            in
                if (not(tiposIguales typeExp typeVar)) then
                    error(printRef name ^ " con tipo incompatible",pos)
                else
                    let
                        val venv' = tabRInserta(name,Var {ty=typeVar},venv)
                    in
                        (venv',tenv,[])
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
                fun genTipo {name = s, typ = t, ...} =
                    let val tTipo = (case t of
                                         NameTy n => (case tabBusca (n,tenv) of
                                                          NONE => raise Fail (printRef s ^ " tiene un tipo inexistente")
                                                        | SOME ttipo => ttipo)
                                       | _ => raise Fail (printRef s ^ " tiene un tipo incorrecto"))
                    in (s,tTipo) end

                fun putVars ([], env) = env  
                  | putVars ((((s,vtype))::xs), env) = tabRInserta(s, Var {ty = vtype}, putVars (xs,env))

                fun putFuncs ([], env) = env  
                  | putFuncs ((((s,ftype),_)::xs), env) = tabRInserta(s, ftype, putFuncs (xs,env))

                (* esta funcion la utilizaremos para agregar cada una de las funciones de fs a venv *)
                fun genEnvEntry  ({name = s, params = ps, result = NONE, body = exp}, pos) =
                    let val fmlPairs = map genTipo ps
                        val fmls = map (#2) fmlPairs
                        val f = Func {level = (), label = tigertemp.newlabel()^s, formals = fmls, result = TUnit, extern = false}
                    in
                        ((s,f),fmlPairs)
                    end
                  | genEnvEntry ({name = s, params = ps, result = (SOME n), body = exp}, pos) =
                    let
                        val ttipo = (case tabBusca (n,tenv) of
                                        NONE => error(printRef n ^ " tiene un tipo de retorno inexistente", pos)
                                      | SOME t => t)
                        val fmlPairs = map genTipo ps
                        val fmls = map (#2) fmlPairs
                        val f = Func {level = (), label = tigertemp.newlabel()^s, formals = fmls, result = ttipo, extern = false}
                    in
                        ((s,f),fmlPairs)
                    end


                fun checkBodies _ [] [] = ()
                  | checkBodies venv (x::xs) (({name = s, params = ps, result = NONE, body = exp}, pos)::fs) =
                    let val venv' = putVars (x,venv)
                        val {ty = tBody, ...} = transExp (venv',tenv) exp
                    in
                        if not(tiposIguales TUnit tBody) then
                            error(printRef s ^ " tiene un tipo de retorno inválido", pos)
                        else
                            checkBodies venv xs fs
                    end
                  | checkBodies venv (x::xs) (({name = s, params = ps, result = (SOME n), body = exp}, pos)::fs) =
                    let
                        val ttipo = (case tabBusca (n,tenv) of
                                         NONE => error(printRef n ^ " tiene un tipo de retorno inexistente", pos)
                                       | SOME t => t)
                                        
                        val venv' = putVars (x,venv)
                        val {ty = tBody, ...} = transExp (venv',tenv) exp
                    in
                        if not(tiposIguales ttipo tBody) then
                            error(printRef s ^ " tiene un tipo de retorno inválido", pos)
                        else
                            checkBodies venv xs fs
                    end
                  | checkBodies _ _ _ = raise Fail "error interno: chequeo de tipos en función\n"
                  

                val listFuncEntriesAndOthers = map genEnvEntry fs
                val formals = map (#2) listFuncEntriesAndOthers
                val venv' = putFuncs (listFuncEntriesAndOthers,venv)
                val _ = checkBodies venv' formals fs
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

                (* procesa la lista ordenada dada por el topsort, no procesa Arrays ni Records *)
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
                        
                (* procesa records y arrays, además, posiblemente, le da tipo a los
                NameTy que están definidos en base a records o arrays *)
                fun segundaPasada batch recs env =
                    let
                        fun buscaEnv env' t =
                            case List.find (fn {name, ...} => name = t) batch of
                                SOME {name, ...} => TTipo(name, ref NONE)
                              | _ => case tabBusca(t, env) of
                                         SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                                       | SOME tt => tt
                                       | _ => (case tabBusca(t, env') of
                                                   SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                                                 | SOME tt => tt
                                                 | _ => error (printRef t^" es un tipo inexistente", firstNL))

                        fun precs [] env' = env'
                          | precs ({name, ty=RecordTy lf} :: t) env' =
                            let
                                val lf' = List.foldl (fn ({name, typ=NameTy t, ...}, l) => (name, buscaEnv env' t) :: l
                                                     | (_, l) => l) [] lf
                                val (_, lf'')= List.foldl (fn ((x,y),(n,l)) => (n+1, (x,y,n)::l)) (0,[]) lf'
                                val env'' = tabRInserta (name, TRecord (lf'', ref ()), env')
                            in precs t env'' end

                          | precs ({name, ty=ArrayTy ty} :: t) env' =
                            precs t (tabRInserta (name, TArray (buscaEnv env' ty, ref ()), env'))
                          
                          | precs ({name, ty = NameTy ty} :: t) env' = 
                            precs t (tabRInserta (name, buscaEnv env' ty, env'))

                    in precs batch (fromTab env) end
                        
                (* reemplaza los tipos "punteros" a NONE, por punteros al record del cual
                son miembros y pone los tipos definitivos en los NameTy *)
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

                        val env'' = segundaPasada batch recs env'

                        val _ = (print("Tabla en el 2º procesa: ") ; printTab (env''); print("\n"))

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
					result= SOME "int", body=ex}, 0)]],
		    body=UnitExp 0}, 0)
	val _ = transExp(tab_vars, tab_tipos) main
	(* val _ = transExp(tab_vars, tab_tipos) ex (\* despues hay que cambiarlo *\) *)
    in	print "bien!\n" end
end
