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

end
