structure eje2 :> eje2  =
struct
open tigerabs

fun  cantprints (CallExp ({func = "print", args = []}, ln)) = raise Fail ("cantprints: print sin argumentos "^Int.toString(ln)^"\n")
   | cantprints (CallExp ({func = "print", args = [StringExp _]},_)) = 0
   | cantprints (CallExp ({func = "print", args = x::(y::xs)}, ln)) = raise Fail ("cantprints: print con más de un argumento "^Int.toString(ln)^"\n")
   | cantprints (CallExp ({func = "print", args = [x]},_)) = cantprints x + 1
   | cantprints (CallExp ({args = xs, ...},_)) = foldl(fn (x,n) => cantprints x + n) 0 xs
   | cantprints (VarExp (var,_)) = cantprintsVar var
   | cantprints (UnitExp _) = 0
   | cantprints (NilExp _) = 0
   | cantprints (IntExp _) = 0
   | cantprints (StringExp _) = 0
   | cantprints (OpExp ({right = e1, left = e2, ...},_)) = cantprints e1 + cantprints e2
   | cantprints (RecordExp ({fields = xs, ...},_)) = foldl(fn ((_,e),n) => cantprints e + n) 0 xs
   | cantprints (SeqExp (xs,_)) = foldl(fn (x,n) => cantprints x + n) 0 xs
   | cantprints (AssignExp ({var = var, exp = e},_)) = cantprintsVar var + cantprints e
   | cantprints (IfExp ({test = e1, then' = e2, else' = (SOME e3)},_)) = cantprints e1 + cantprints e2 + cantprints e3
   | cantprints (IfExp ({test = e1, then' = e2, else' = NONE},_)) = cantprints e1 + cantprints e2
   | cantprints (WhileExp ({test = e1, body = e2}, _)) = cantprints e1 + cantprints e2
   | cantprints (ForExp ({lo = e1, hi = e2, body = e3, ...}, _)) = cantprints e1 + cantprints e2 + cantprints e3
   | cantprints (LetExp ({decs = decls, body = e1}, _)) =  foldr(fn (x,n) => cantprintsDecs x + n) 0 decls + cantprints e1
   | cantprints (BreakExp _) = 0
   | cantprints (ArrayExp ({size = e1, init = e2, ...}, _)) = cantprints e1 + cantprints e2

and cantprintsDecs (FunctionDec xs) = foldl(fn (({body = e, ...},_),n) => cantprints e + n) 0 xs
  | cantprintsDecs (VarDec ({init = e, ...},_)) = cantprints e
  | cantprintsDecs (TypeDec _) = 0

and cantprintsVar (SimpleVar _) = 0
  | cantprintsVar (FieldVar (v,_)) = cantprintsVar v
  | cantprintsVar (SubscriptVar (v,e)) = cantprintsVar v + cantprints e



fun cantplus (VarExp (v,_)) = cantplusVar v
  | cantplus (UnitExp _) = 0
  | cantplus (NilExp _) = 0
  | cantplus (IntExp _) = 0
  | cantplus (StringExp _) = 0
  | cantplus (CallExp ({func = _, args = expL},_)) = foldr (fn (e,n) => cantplus e + n) 0 expL
  | cantplus (OpExp ({left = e1, oper = PlusOp, right = e2},_)) = 1 + cantplus e1 + cantplus e2
  | cantplus (RecordExp ({fields = flds, typ = _},_)) = foldr (fn ((_,e),n) => cantplus e + n) 0 flds
  | cantplus (SeqExp (expL,_)) = foldr (fn (e,n) => cantplus e + n) 0 expL
  | cantplus (AssignExp ({var = v, exp = e},_)) = cantplusVar v + cantplus e
  | cantplus (IfExp ({test = e1, then' = e2, else' = NONE},_)) = cantplus e1 + cantplus e2
  | cantplus (IfExp ({test = e1, then' = e2, else' = (SOME e3)},_)) = cantplus e1 + cantplus e2 + cantplus e3
  | cantplus (WhileExp ({test = e1, body = e2},_)) = cantplus e1 + cantplus e2
  | cantplus (ForExp ({lo = e1, hi = e2, body = e3, ...},_)) = cantplus e1 + cantplus e2 + cantplus e3
  | cantplus (LetExp ({decs = decls, body = e},_)) = foldr (fn (d,n) => cantplusDecs d + n) 0 decls + cantplus e
  | cantplus (BreakExp _) = 0
  | cantplus (ArrayExp ({typ = _, size = e1, init = e2},_)) = cantplus e1 + cantplus e2

and cantplusVar (SimpleVar _) = 0
  | cantplusVar (FieldVar (v,_)) = cantplusVar v
  | cantplusVar (SubscriptVar (v,e)) = cantplusVar v + cantplus e

and cantplusDecs (FunctionDec decs) = foldr (fn (d,n) => cantplusDecsAux d + n) 0 decs
  | cantplusDecs (VarDec ({init = e, ...},_)) = cantplus e
  | cantplusDecs (TypeDec _) = 0

and cantplusDecsAux ({body = e, ...},_) = cantplus e

end
