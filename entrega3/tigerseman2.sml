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
	    (* NOSOTROS - FALTA *)
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
		    {exp=nilExp(), ty = resultType}
		else
		    error(printRef f ^ " es llamada con argumento/s inválido/s", nl)
	    end	  
          | trexp(OpExp({left, oper=EqOp, right}, nl)) =
	    let
		val {exp=expl, ty=tyl} = trexp left
		val {exp=expr, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
		    {exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=EqOp,right=expr} else binOpIntRelExp {left=expl,oper=EqOp,right=expr}, ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper=NeqOp, right}, nl)) = 
	    let
		val {exp=expl, ty=tyl} = trexp left
		val {exp=expr, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr andalso not (tyl=TNil andalso tyr=TNil) andalso tyl<>TUnit then 
		    {exp=if tiposIguales tyl TString then binOpStrExp {left=expl,oper=NeqOp,right=expr} else binOpIntRelExp {left=expl,oper=NeqOp,right=expr}, ty=TInt}
		else error("Tipos no comparables", nl)
	    end
	  | trexp(OpExp({left, oper, right}, nl)) = 
	    let
		val {exp=expl, ty=tyl} = trexp left
		val {exp=expr, ty=tyr} = trexp right
	    in
		if tiposIguales tyl tyr then
		    case oper of
			PlusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
		      | MinusOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
		      | TimesOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
		      | DivideOp => if tipoReal tyl=TInt then {exp=binOpIntExp {left=expl, oper=oper, right=expr},ty=TInt} else error("Error de tipos", nl)
		      | LtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
				else error("Error de tipos", nl)
		      | LeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then 
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
				else error("Error de tipos", nl)
		      | GtOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
				else error("Error de tipos", nl)
		      | GeOp => if tipoReal tyl=TInt orelse tipoReal tyl=TString then
				    {exp=if tipoReal tyl=TInt then binOpIntRelExp {left=expl,oper=oper,right=expr} else binOpStrExp {left=expl,oper=oper,right=expr},ty=TInt} 
				else error("Error de tipos", nl)
		      | _ => raise Fail "No debería pasar! (3)"
		else error("Error de tipos", nl)
	    end
	  | trexp(RecordExp({fields, typ}, nl)) =
            (* Caso no mergeado *)
	    let
		(* Traducir cada expresión de fields *)
		val tfields = map (fn (sy,ex) => (sy, trexp ex)) fields

		(* Buscar el tipo *)
		val (tyr, cs) = case tabBusca(typ, tenv) of
				    SOME t => (case tipoReal t of
						   TRecord (cs, u) => (TRecord (cs, u), cs)
						 | _ => error(typ^" no es de tipo record", nl))
				  | NONE => error("Tipo inexistente ("^typ^")", nl)
				            
		(* Verificar que cada campo esté en orden y tenga una expresión del tipo que corresponde *)
		fun verificar _ [] [] = []
		  | verificar _ (c::cs) [] = error("Faltan campos", nl)
		  | verificar _ [] (c::cs) = error("Sobran campos", nl)
		  | verificar n ((s,t,_)::cs) ((sy,{exp,ty})::ds) =
		    if s<>sy then error("Error de campo", nl)
		    else if tiposIguales ty t then (exp, n)::(verificar (n+1) cs ds)
		    else error("Error de tipo del campo "^s, nl)
		val lf = verificar 0 cs tfields
	    in
		{exp=recordExp lf, ty=tyr}
            end
	  | trexp(SeqExp(s, nl)) =
	    let	val lexti = map trexp s
		val exprs = map (fn{exp, ty} => exp) lexti
		val {exp, ty=tipo} = hd(rev lexti)
	    in	{ exp=seqExp (exprs), ty=tipo } end
	  | trexp(AssignExp({var = SimpleVar s, exp = e}, nl)) =
	    (*NOSOTROS*)
            let
                val {ty = expType, ...} = trexp e
                val {ty = varType, ...} = trvar ((SimpleVar s),nl)
            in
                case tabBusca(s, venv) of
                    SOME (IntReadOnly _) => error("Intentando asignar variable Read Only",nl)
                  | _ => 
                    if tiposIguales expType varType then
                        {exp=nilExp(), ty = TUnit }
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
                    {exp=nilExp(), ty = TUnit }
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
	    let
		val ttest = trexp test
		val tbody = trexp body
	    in
		if tipoReal (#ty ttest) = TInt andalso #ty tbody = TUnit then {exp=whileExp {test=(#exp ttest), body=(#exp tbody), lev=topLevel()}, ty=TUnit}
		else if tipoReal (#ty ttest) <> TInt then error("Error de tipo en la condición", nl)
		else error("El cuerpo de un while no puede devolver un valor", nl)
	    end
	  | trexp(ForExp({var, lo = e1, hi = e2, body = e3, ...}, nl)) =
	    (* NOSOTROS *)
            let
                val {ty = typeLo, ...} = trexp e1
                val {ty = typeHi, ...} = trexp e2
                (* val venv' = tabRInserta (var,IntReadOnly,venv) *)
                val venv' = venv (* echo de manera temporal *)
                val {ty = typeBody, ...} = transExp (venv', tenv) e3
            in
                if(not((tiposIguales typeLo typeHi) andalso (tiposIguales TInt typeLo)))
                then error("expresión/es con tipo/s inválido/s",nl)
                else
                    if(not(tiposIguales typeBody TUnit))
                    then error("el cuerpo del bucle tiene tipo inválido",nl)
                    else
	                {exp=nilExp(), ty=TUnit}
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
	    {exp=nilExp(), ty=TUnit} (*COMPLETAR*)
	  | trexp(ArrayExp({typ, size = e1, init = e2}, nl)) =
            (*NOSOTROS*)
            let
                val {ty = typeSize, ...} = trexp e1
                val {ty = typeInit, ...} = trexp e2 (* la expresion init siempre existe?, puede ser cualquier tipo? *)
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
                {exp = nilExp(), ty = TArray(typeInit,u)}
            end
	and trvar(SimpleVar s, nl) =
            (* NOSOTROS *)
            let
		val varType =
		    case tabBusca (s, venv) of
			SOME (Var {ty = t, ...}) => t
                      | SOME (IntReadOnly _) => TInt
                      | SOME _ => error (s ^ " es de tipo inválido", nl)
		      | NONE => error(s ^ " no fue declarada", nl)
            in
		{exp=nilExp(), ty=varType}
            end
	  | trvar(FieldVar(v, s), nl) =
            (*NOSOTROS*)
            let
                val {ty = typeVar, ...} = trvar (v,nl)
            in
                (case typeVar of
                     TRecord (xs,_) =>
                     (case List.find(fn (nameMember,_,_) => nameMember = s) xs of
                          SOME (_,t,_) => {exp = nilExp(), ty = t}
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
                    case typeVar of
                        TArray (t,_) => {exp = nilExp(), ty = t}
                      | _ => error("se intenta acceder a algo que no es un arreglo",nl)
                
            end
        and trdec (venv, tenv) (VarDec ({name,escape,typ=NONE,init},pos)) = 
	    (*NOSOTROS*)
            let
                val {ty = typeExp, ...} = transExp (venv, tenv) init
                val venv' = case typeExp of
                                TNil => error (printRef name ^ " no es posible inferir su tipo", pos)
                              (* | _ => tabInserta(name,Var {ty=typeExp},venv) *)
                              | _ => venv (*ECHO DE MANERA TEMPORAL*)
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
                        (* val venv' = tabInserta(name,Var {ty=typeVar}, venv) *)
                        val venv' = venv  (*ECHO DE MANERA TEMPORAL*)
                    in
                        (venv',tenv,[])
                    end
            end
	  | trdec (venv,tenv) (FunctionDec fs) =
            (*NO SE PUEDE MERGEAR*)
	    (venv, tenv, [])
	  | trdec (venv,tenv) (TypeDec ts) =
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
                        val lrecs = buscaArrRecords lt
                        fun genP [] res = res
                           |genP ({name, ty = NameTy s} :: t) res =
                            genP t ((s,name)::res)
                           |genP ({name, ty = ArrayTy s} :: t) res =
                            genP t ((s,name) :: res)
                           |genP ({name,ty = RecordTy lf} :: t) res =
                            let fun recorre ({typ = NameTy x, ...} :: t) =
                                    (case List.find ((op = rs x) o #name) lrecs  of
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
                fun procesaInicial [] decs recs env = env
                  | procesaInicial (sorted as (h::t)) decs recs env =
                    let
                        fun filt h {name, ty=NameTy t} = h = t
                          | filt h {name, ty=ArrayTy t} = h = t
                          | filt h {name, ty=RecordTy lt} = List.exists (fn {name, ...} => h = name) lt
                        val (ps,ps') = List.partition (filt h) decs
                        val ttopt = case List.find (fn {name,ty} => name = h) recs of
                                        SOME _ => NONE
                                      | NONE => (case tabBusca(h, env) of
                                                     SOME t => SOME t
                                                   | _ => raise error (printRef h^" es un tipo inexistente", firstNL))
                        val env' = case ttopt of
                                       SOME tt => List.foldr (fn ({name, ty=NameTy _}, env) => tabInserta(name, tt, env)
                                                             | (_, env) => env) env ps
                                     | _ => env
                    in procesaInicial t ps' recs env' end
                        
                (* procesa records y arrays *)
                fun procRecordsArrays recs env =
                    let
                        fun buscaEnv env' t =
                            case tabBusca(t, env) of
                                SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                              | SOME tt => tt
                              | _ => (case tabBusca(t, env') of
                                          SOME (x as (TRecord _)) => TTipo (t, ref (SOME x))
                                        | SOME tt => tt
                                        | _ => case List.find (fn {name, ...} => name = t) recs of
                                                   SOME {name, ...} => TTipo(name, ref NONE)
                                                 | _ => error (printRef t^" es un tipo inexistente", firstNL))
                        fun precs [] env' = env'
                          | precs ({name, ty=RecordTy lf} :: t) env' =
                            let
                                val lf' = List.foldl (fn ({name, typ=NameTy t, ...}, l) => (name, buscaEnv env' t) :: l
                                                     | (_, l) => l) [] lf
                                val (_, lf'')= List.foldl (fn ((x,y),(n,l)) => (n+1, (x,y,n)::l)) (0,[]) lf'
                                val env'' = tabInserta (name, TRecord (lf'', ref ()), env')
                            in precs t env'' end

                          | precs ({name, ty=ArrayTy ty} :: t) env' =
                            precs t (tabInserta (name, TArray (buscaEnv env' ty, ref ()), env'))

                          | precs _ _ = error ("error interno: proceso de Records", firstNL)
                    in precs recs (fromTab env) end
                        
                (* reemplaza los tipos "punteros" a NONE, por punteros al record del cual son miembros *)
                fun fijaNONE [] env = env                  
                  (*No se daría nunca*)
                  | fijaNONE ((name, TArray (TTipo (s, ref NONE), u)) :: t) env =
                    (case tabBusca(s, env) of
                         SOME (r as (TRecord _)) => fijaNONE t (tabRInserta (name, TArray (TTipo (s, ref (SOME r)), u) , env))
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
                  | fijaNONE (_ :: t) env = fijaNONE t env
                                                   
                (* Fija tipos en un batch *)
                fun fijatipos batch env =
                    let
                        val pares = genPares batch
                        val ordered = topsort.topsort pares
                        val recs = buscaArrRecords batch
                        val env' = procesaInicial ordered batch recs env
                        val env'' = procRecordsArrays recs env'
                        val env'''= fijaNONE (tabAList env'') env''                                                
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
					result=NONE, body=ex}, 0)]],
		    body=UnitExp 0}, 0)
	val _ = transExp(tab_vars, tab_tipos) main
    in	print "bien!\n" end
end
