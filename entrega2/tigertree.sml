structure tigertree =
struct
datatype exp = CONST of int
	     | NAME of tigertemp.label (* dirección de memoria de un label *)
	     | TEMP of tigertemp.temp (* registro *)
	     | BINOP of binop*exp*exp
	     | MEM of exp (* dirección de memoria de exp (lado izquierdo) o lo que esta contenido en exp (lado derecho) *)
	     | CALL of exp*exp list (* llamada a función *)
	     | ESEQ of stm*exp
     and stm = MOVE of exp*exp
	     | EXP of exp (* evalúa la expresión, pero no devuelve el resultado *)
	     | JUMP of exp*tigertemp.label list
	     | CJUMP of relop*exp*exp*tigertemp.label*tigertemp.label
	     | SEQ of stm*stm
	     | LABEL of tigertemp.label (* nombre de un label *)
     and binop = PLUS | MINUS | MUL | DIV | AND | OR
	       | LSHIFT | RSHIFT | ARSHIFT | XOR
     and relop = EQ | NE | LT | GT | LE | GE | ULT | ULE
	       | UGT | UGE

fun notRel EQ = NE
  | notRel NE = EQ
  | notRel LT = GE
  | notRel GE = LT
  | notRel GT = LE
  | notRel LE = GT
  | notRel ULT = UGE
  | notRel UGE = ULT
  | notRel ULE = UGT
  | notRel UGT = ULE
end
