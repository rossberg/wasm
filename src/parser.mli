type token =
  | INT of (string)
  | FLOAT of (string)
  | TEXT of (string)
  | VAR of (int)
  | TYPE of (Types.value_type)
  | LPAR
  | RPAR
  | NOP
  | BLOCK
  | IF
  | LOOP
  | LABEL
  | BREAK
  | SWITCH
  | CASE
  | FALLTHRU
  | CALL
  | DISPATCH
  | RETURN
  | DESTRUCT
  | GETLOCAL
  | SETLOCAL
  | GETGLOBAL
  | SETGLOBAL
  | GETMEMORY of (Syntax.memop)
  | SETMEMORY of (Syntax.memop)
  | CONST of (Types.value_type)
  | UNARY of (Syntax.unop)
  | BINARY of (Syntax.binop)
  | COMPARE of (Syntax.relop)
  | CONVERT of (Syntax.cvt)
  | FUNC
  | PARAM
  | RESULT
  | LOCAL
  | MODULE
  | GLOBAL
  | IMPORT
  | EXPORT
  | TABLE
  | MEMORY
  | DEFINE
  | INVOKE
  | EOF

val script :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Script.script
