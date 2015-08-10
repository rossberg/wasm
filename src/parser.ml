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

open Parsing;;
let _ = parse_error;;
# 6 "parser.mly"
open Source
open Syntax
open Script

let position_to_pos position =
  { file = position.Lexing.pos_fname;
    line = position.Lexing.pos_lnum;
    column = position.Lexing.pos_cnum - position.Lexing.pos_bol
  }

let positions_to_region position1 position2 =
  { left = position_to_pos position1;
    right = position_to_pos position2
  }

let at () =
  positions_to_region (Parsing.symbol_start_pos ()) (Parsing.symbol_end_pos ())
let ati i =
  positions_to_region (Parsing.rhs_start_pos i) (Parsing.rhs_end_pos i)

let parse_error s = Error.error Source.no_region s

let literal at s t =
  try
    match t with
    | Types.Int32Type -> Types.Int32 (Int32.of_string s) @@ at
    | Types.Int64Type -> Types.Int64 (Int64.of_string s) @@ at
    | Types.Float32Type -> Types.Float32 (float_of_string s) @@ at
    | Types.Float64Type -> Types.Float64 (float_of_string s) @@ at
  with _ -> Error.error at "constant out of range"
# 81 "parser.ml"
let yytransl_const = [|
  262 (* LPAR *);
  263 (* RPAR *);
  264 (* NOP *);
  265 (* BLOCK *);
  266 (* IF *);
  267 (* LOOP *);
  268 (* LABEL *);
  269 (* BREAK *);
  270 (* SWITCH *);
  271 (* CASE *);
  272 (* FALLTHRU *);
  273 (* CALL *);
  274 (* DISPATCH *);
  275 (* RETURN *);
  276 (* DESTRUCT *);
  277 (* GETLOCAL *);
  278 (* SETLOCAL *);
  279 (* GETGLOBAL *);
  280 (* SETGLOBAL *);
  288 (* FUNC *);
  289 (* PARAM *);
  290 (* RESULT *);
  291 (* LOCAL *);
  292 (* MODULE *);
  293 (* GLOBAL *);
  294 (* IMPORT *);
  295 (* EXPORT *);
  296 (* TABLE *);
  297 (* MEMORY *);
  298 (* DEFINE *);
  299 (* INVOKE *);
    0 (* EOF *);
    0|]

let yytransl_block = [|
  257 (* INT *);
  258 (* FLOAT *);
  259 (* TEXT *);
  260 (* VAR *);
  261 (* TYPE *);
  281 (* GETMEMORY *);
  282 (* SETMEMORY *);
  283 (* CONST *);
  284 (* UNARY *);
  285 (* BINARY *);
  286 (* COMPARE *);
  287 (* CONVERT *);
    0|]

let yylhs = "\255\255\
\002\000\003\000\003\000\004\000\004\000\005\000\006\000\006\000\
\007\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
\008\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
\008\000\008\000\008\000\008\000\008\000\008\000\008\000\008\000\
\008\000\009\000\009\000\010\000\010\000\012\000\012\000\013\000\
\013\000\011\000\011\000\014\000\014\000\014\000\014\000\014\000\
\015\000\016\000\016\000\016\000\016\000\016\000\017\000\017\000\
\018\000\018\000\018\000\018\000\019\000\019\000\001\000\000\000"

let yylen = "\002\000\
\001\000\000\000\002\000\001\000\001\000\001\000\000\000\002\000\
\003\000\001\000\003\000\004\000\003\000\002\000\002\000\003\000\
\001\000\003\000\003\000\004\000\002\000\003\000\002\000\003\000\
\002\000\003\000\002\000\003\000\002\000\002\000\003\000\003\000\
\002\000\000\000\002\000\001\000\003\000\000\000\001\000\006\000\
\004\000\001\000\002\000\000\000\001\000\005\000\005\000\005\000\
\004\000\000\000\002\000\005\000\005\000\005\000\004\000\001\000\
\001\000\004\000\005\000\004\000\000\000\002\000\002\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\064\000\056\000\057\000\000\000\000\000\
\000\000\000\000\000\000\000\000\062\000\063\000\000\000\000\000\
\045\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\010\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\049\000\000\000\000\000\
\000\000\051\000\055\000\058\000\000\000\035\000\060\000\000\000\
\000\000\014\000\015\000\006\000\000\000\000\000\000\000\000\000\
\021\000\000\000\000\000\023\000\000\000\025\000\000\000\027\000\
\000\000\004\000\005\000\029\000\030\000\000\000\000\000\033\000\
\001\000\000\000\000\000\000\000\000\000\009\000\037\000\000\000\
\000\000\000\000\059\000\011\000\000\000\016\000\000\000\042\000\
\018\000\000\000\019\000\000\000\008\000\022\000\024\000\026\000\
\028\000\031\000\032\000\003\000\000\000\000\000\000\000\000\000\
\000\000\000\000\012\000\000\000\043\000\020\000\046\000\047\000\
\048\000\052\000\053\000\054\000\000\000\041\000\000\000\039\000\
\000\000\040\000"

let yydgoto = "\002\000\
\004\000\090\000\091\000\084\000\074\000\075\000\025\000\052\000\
\026\000\017\000\105\000\137\000\106\000\018\000\020\000\021\000\
\006\000\007\000\008\000"

let yysindex = "\008\000\
\009\255\000\000\255\254\000\000\000\000\000\000\009\255\027\000\
\026\255\035\255\012\255\024\255\000\000\000\000\108\255\038\255\
\000\000\058\255\042\255\035\255\060\255\062\255\038\255\160\255\
\038\255\064\255\000\000\038\255\038\255\038\255\038\255\054\255\
\038\255\054\255\054\255\038\255\054\255\054\255\054\255\054\255\
\054\255\038\255\038\255\048\255\038\255\038\255\038\255\038\255\
\068\255\068\255\068\255\073\255\038\255\000\000\068\255\054\255\
\054\255\000\000\000\000\000\000\078\255\000\000\000\000\038\255\
\038\255\000\000\000\000\000\000\038\255\080\255\038\255\038\255\
\000\000\054\255\038\255\000\000\038\255\000\000\038\255\000\000\
\038\255\000\000\000\000\000\000\000\000\038\255\038\255\000\000\
\000\000\068\255\081\255\082\255\083\255\000\000\000\000\084\255\
\086\255\087\255\000\000\000\000\038\255\000\000\136\255\000\000\
\000\000\080\255\000\000\038\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\026\255\026\255\026\255\035\255\
\035\255\035\255\000\000\048\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\069\255\000\000\071\255\000\000\
\088\255\000\000"

let yyrindex = "\000\000\
\096\000\000\000\000\000\000\000\000\000\000\000\096\000\000\000\
\091\255\092\255\000\000\093\255\000\000\000\000\000\000\007\255\
\000\000\000\000\000\000\092\255\000\000\000\000\093\255\000\000\
\010\255\000\000\000\000\000\000\000\000\000\000\000\000\095\255\
\000\000\000\000\000\000\093\255\097\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\104\255\104\255\104\255\000\000\010\255\000\000\104\255\105\255\
\105\255\000\000\000\000\000\000\000\000\000\000\000\000\093\255\
\000\000\000\000\000\000\000\000\093\255\000\000\093\255\000\000\
\000\000\077\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\104\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\106\255\000\000\000\000\000\000\
\000\000\000\000\000\000\093\255\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\091\255\091\255\091\255\092\255\
\092\255\092\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\107\255\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\209\255\255\255\013\000\210\255\247\255\000\000\
\249\255\227\255\009\000\000\000\000\000\197\255\005\000\241\255\
\000\000\000\000\133\000"

let yytablesize = 191
let yytable = "\016\000\
\066\000\067\000\092\000\093\000\058\000\005\000\053\000\096\000\
\001\000\097\000\098\000\005\000\022\000\036\000\003\000\061\000\
\034\000\062\000\064\000\065\000\016\000\016\000\036\000\070\000\
\023\000\034\000\014\000\109\000\073\000\024\000\009\000\015\000\
\080\000\081\000\010\000\085\000\086\000\087\000\088\000\011\000\
\019\000\012\000\116\000\024\000\069\000\095\000\071\000\072\000\
\082\000\083\000\076\000\077\000\078\000\079\000\068\000\101\000\
\100\000\127\000\128\000\129\000\104\000\102\000\108\000\107\000\
\054\000\110\000\059\000\111\000\060\000\112\000\063\000\113\000\
\089\000\009\000\024\000\134\000\114\000\115\000\055\000\094\000\
\056\000\057\000\007\000\007\000\099\000\103\000\136\000\117\000\
\118\000\119\000\120\000\123\000\121\000\122\000\138\000\061\000\
\104\000\044\000\050\000\034\000\126\000\017\000\007\000\135\000\
\130\000\131\000\132\000\016\000\016\000\016\000\002\000\007\000\
\013\000\038\000\125\000\027\000\028\000\029\000\030\000\031\000\
\032\000\033\000\133\000\016\000\034\000\035\000\036\000\037\000\
\038\000\039\000\040\000\041\000\042\000\043\000\044\000\045\000\
\046\000\047\000\048\000\013\000\049\000\050\000\051\000\027\000\
\028\000\029\000\030\000\031\000\032\000\033\000\124\000\000\000\
\034\000\035\000\036\000\037\000\038\000\039\000\040\000\041\000\
\042\000\043\000\044\000\045\000\046\000\047\000\048\000\027\000\
\028\000\029\000\030\000\031\000\032\000\033\000\000\000\000\000\
\034\000\035\000\036\000\037\000\038\000\039\000\040\000\041\000\
\042\000\043\000\044\000\045\000\046\000\047\000\048\000"

let yycheck = "\009\000\
\030\000\031\000\050\000\051\000\020\000\001\000\016\000\055\000\
\001\000\056\000\057\000\007\000\001\001\007\001\006\001\023\000\
\007\001\025\000\028\000\029\000\030\000\031\000\016\001\033\000\
\001\001\016\001\000\000\074\000\036\000\006\001\032\001\006\001\
\042\000\043\000\036\001\045\000\046\000\047\000\048\000\041\001\
\006\001\043\001\090\000\006\001\032\000\053\000\034\000\035\000\
\001\001\002\001\038\000\039\000\040\000\041\000\001\001\065\000\
\064\000\117\000\118\000\119\000\070\000\069\000\072\000\071\000\
\007\001\075\000\007\001\077\000\007\001\079\000\007\001\081\000\
\005\001\032\001\006\001\007\001\086\000\087\000\037\001\007\001\
\039\001\040\001\006\001\007\001\007\001\006\001\016\001\007\001\
\007\001\007\001\007\001\101\000\007\001\007\001\007\001\000\000\
\106\000\007\001\007\001\007\001\108\000\007\001\006\001\133\000\
\120\000\121\000\122\000\117\000\118\000\119\000\007\001\007\001\
\007\001\007\001\106\000\008\001\009\001\010\001\011\001\012\001\
\013\001\014\001\124\000\133\000\017\001\018\001\019\001\020\001\
\021\001\022\001\023\001\024\001\025\001\026\001\027\001\028\001\
\029\001\030\001\031\001\007\000\033\001\034\001\035\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\015\001\255\255\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\031\001\008\001\
\009\001\010\001\011\001\012\001\013\001\014\001\255\255\255\255\
\017\001\018\001\019\001\020\001\021\001\022\001\023\001\024\001\
\025\001\026\001\027\001\028\001\029\001\030\001\031\001"

let yynames_const = "\
  LPAR\000\
  RPAR\000\
  NOP\000\
  BLOCK\000\
  IF\000\
  LOOP\000\
  LABEL\000\
  BREAK\000\
  SWITCH\000\
  CASE\000\
  FALLTHRU\000\
  CALL\000\
  DISPATCH\000\
  RETURN\000\
  DESTRUCT\000\
  GETLOCAL\000\
  SETLOCAL\000\
  GETGLOBAL\000\
  SETGLOBAL\000\
  FUNC\000\
  PARAM\000\
  RESULT\000\
  LOCAL\000\
  MODULE\000\
  GLOBAL\000\
  IMPORT\000\
  EXPORT\000\
  TABLE\000\
  MEMORY\000\
  DEFINE\000\
  INVOKE\000\
  EOF\000\
  "

let yynames_block = "\
  INT\000\
  FLOAT\000\
  TEXT\000\
  VAR\000\
  TYPE\000\
  GETMEMORY\000\
  SETMEMORY\000\
  CONST\000\
  UNARY\000\
  BINARY\000\
  COMPARE\000\
  CONVERT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : Types.value_type) in
    Obj.repr(
# 68 "parser.mly"
         ( _1 @@ at() )
# 332 "parser.ml"
               : 'value_type))
; (fun __caml_parser_env ->
    Obj.repr(
# 71 "parser.mly"
                ( [] )
# 338 "parser.ml"
               : 'value_type_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'value_type) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'value_type_list) in
    Obj.repr(
# 72 "parser.mly"
                               ( _1 :: _2 )
# 346 "parser.ml"
               : 'value_type_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 79 "parser.mly"
        ( _1 )
# 353 "parser.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 80 "parser.mly"
          ( _1 )
# 360 "parser.ml"
               : 'literal))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 85 "parser.mly"
    ( try int_of_string _1 @@ at() with _ ->
        Error.error (at ()) "invalid variable index" )
# 368 "parser.ml"
               : 'var))
; (fun __caml_parser_env ->
    Obj.repr(
# 89 "parser.mly"
                ( [] )
# 374 "parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var_list) in
    Obj.repr(
# 90 "parser.mly"
                 ( _1 :: _2 )
# 382 "parser.ml"
               : 'var_list))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr1) in
    Obj.repr(
# 94 "parser.mly"
                    ( _2 @@ at() )
# 389 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 97 "parser.mly"
        ( Nop )
# 395 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 98 "parser.mly"
                         ( Block (_2 :: _3) )
# 403 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
                      ( If (_2, _3, _4) )
# 412 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 100 "parser.mly"
                 ( If (_2, _3, Nop @@ ati 1) )
# 420 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr_block) in
    Obj.repr(
# 101 "parser.mly"
                    ( Loop _2 )
# 427 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr_block) in
    Obj.repr(
# 102 "parser.mly"
                     ( Label _2 )
# 434 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 103 "parser.mly"
                        ( Break (_2, _3) )
# 442 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    Obj.repr(
# 104 "parser.mly"
          ( Break (0 @@ at(), []) )
# 448 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'arms) in
    Obj.repr(
# 105 "parser.mly"
                     ( let x, y = _3 in Switch (_2, x, y) )
# 456 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 106 "parser.mly"
                       ( Call (_2, _3) )
# 464 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 107 "parser.mly"
                                ( Dispatch (_2, _3, _4) )
# 473 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 108 "parser.mly"
                     ( Return _2 )
# 480 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var_list) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 109 "parser.mly"
                           ( Destruct (_2, _3) )
# 488 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 110 "parser.mly"
                 ( GetLocal _2 )
# 495 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 111 "parser.mly"
                      ( SetLocal (_2, _3) )
# 503 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'var) in
    Obj.repr(
# 112 "parser.mly"
                  ( GetGlobal _2 )
# 510 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'var) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 113 "parser.mly"
                       ( SetGlobal (_2, _3) )
# 518 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.memop) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 114 "parser.mly"
                   ( GetMemory (_1, _2) )
# 526 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.memop) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 115 "parser.mly"
                        ( SetMemory (_1, _2, _3) )
# 535 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Types.value_type) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'literal) in
    Obj.repr(
# 116 "parser.mly"
                  ( Const (literal (ati 2) _2 _1) )
# 543 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.unop) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 117 "parser.mly"
               ( Unary (_1, _2) )
# 551 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.binop) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 118 "parser.mly"
                     ( Binary (_1, _2, _3) )
# 560 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : Syntax.relop) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 119 "parser.mly"
                      ( Compare (_1, _2, _3) )
# 569 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : Syntax.cvt) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 120 "parser.mly"
                 ( Convert (_1, _2) )
# 577 "parser.ml"
               : 'expr1))
; (fun __caml_parser_env ->
    Obj.repr(
# 123 "parser.mly"
                ( [] )
# 583 "parser.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 124 "parser.mly"
                   ( _1 :: _2 )
# 591 "parser.ml"
               : 'expr_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 127 "parser.mly"
         ( _1 )
# 598 "parser.ml"
               : 'expr_block))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr_list) in
    Obj.repr(
# 128 "parser.mly"
                        ( Block (_1 :: _2 :: _3) @@ at() )
# 607 "parser.ml"
               : 'expr_block))
; (fun __caml_parser_env ->
    Obj.repr(
# 132 "parser.mly"
                ( false )
# 613 "parser.ml"
               : 'fallthru))
; (fun __caml_parser_env ->
    Obj.repr(
# 133 "parser.mly"
             ( true )
# 619 "parser.ml"
               : 'fallthru))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'literal) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr_block) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'fallthru) in
    Obj.repr(
# 137 "parser.mly"
    ( {value = literal (ati 3) _3 Types.Int32Type; expr = _4;
       fallthru = _5} @@ at() )
# 629 "parser.ml"
               : 'arm))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'literal) in
    Obj.repr(
# 140 "parser.mly"
    ( {value = literal (ati 3) _3 Types.Int32Type; expr = Nop @@ ati 4;
       fallthru = true} @@ at() )
# 637 "parser.ml"
               : 'arm))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 144 "parser.mly"
         ( [], _1 )
# 644 "parser.ml"
               : 'arms))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'arm) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'arms) in
    Obj.repr(
# 145 "parser.mly"
             ( let x, y = _2 in _1::x, y )
# 652 "parser.ml"
               : 'arms))
; (fun __caml_parser_env ->
    Obj.repr(
# 153 "parser.mly"
    ( {params = []; results = []; locals = []; body = Nop @@ at()} )
# 658 "parser.ml"
               : 'func_fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr_block) in
    Obj.repr(
# 155 "parser.mly"
    ( {params = []; results = []; locals = []; body = _1} )
# 665 "parser.ml"
               : 'func_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'value_type_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'func_fields) in
    Obj.repr(
# 157 "parser.mly"
    ( {_5 with params = _3 @ _5.params} )
# 673 "parser.ml"
               : 'func_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'value_type_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'func_fields) in
    Obj.repr(
# 159 "parser.mly"
    ( {_5 with results = _3 @ _5.results} )
# 681 "parser.ml"
               : 'func_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'value_type_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'func_fields) in
    Obj.repr(
# 161 "parser.mly"
    ( {_5 with locals = _3 @ _5.locals} )
# 689 "parser.ml"
               : 'func_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'func_fields) in
    Obj.repr(
# 164 "parser.mly"
                               ( _3 @@ at() )
# 696 "parser.ml"
               : 'func))
; (fun __caml_parser_env ->
    Obj.repr(
# 172 "parser.mly"
    ( {funcs = []; exports = []; globals = []; tables = []} )
# 702 "parser.ml"
               : 'module_fields))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'func) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'module_fields) in
    Obj.repr(
# 174 "parser.mly"
    ( {_2 with funcs = _1 :: _2.funcs} )
# 710 "parser.ml"
               : 'module_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'value_type_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'module_fields) in
    Obj.repr(
# 176 "parser.mly"
    ( {_5 with globals = _3 @ _5.globals} )
# 718 "parser.ml"
               : 'module_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'var_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'module_fields) in
    Obj.repr(
# 178 "parser.mly"
    ( {_5 with exports = _3 @ _5.exports} )
# 726 "parser.ml"
               : 'module_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'var_list) in
    let _5 = (Parsing.peek_val __caml_parser_env 0 : 'module_fields) in
    Obj.repr(
# 180 "parser.mly"
    ( {_5 with tables = (_3 @@ ati 3) :: _5.tables} )
# 734 "parser.ml"
               : 'module_fields))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'module_fields) in
    Obj.repr(
# 183 "parser.mly"
                                   ( _3 @@ at() )
# 741 "parser.ml"
               : 'modul))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'func) in
    Obj.repr(
# 185 "parser.mly"
    ( {funcs = [_1]; exports = [0 @@ at()]; globals = []; tables = []} @@ at() )
# 748 "parser.ml"
               : 'modul))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'modul) in
    Obj.repr(
# 192 "parser.mly"
          ( Define _1 @@ at() )
# 755 "parser.ml"
               : 'cmd))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : string) in
    Obj.repr(
# 193 "parser.mly"
                         ( Memory (int_of_string _3) @@ at() )
# 762 "parser.ml"
               : 'cmd))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 194 "parser.mly"
                                   ( Invoke (int_of_string _3, _4) @@ at() )
# 770 "parser.ml"
               : 'cmd))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr_list) in
    Obj.repr(
# 195 "parser.mly"
                               ( Invoke (0, _3) @@ at() )
# 777 "parser.ml"
               : 'cmd))
; (fun __caml_parser_env ->
    Obj.repr(
# 198 "parser.mly"
                ( [] )
# 783 "parser.ml"
               : 'cmd_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'cmd) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'cmd_list) in
    Obj.repr(
# 199 "parser.mly"
                 ( _1 :: _2 )
# 791 "parser.ml"
               : 'cmd_list))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'cmd_list) in
    Obj.repr(
# 203 "parser.mly"
                 ( _1 )
# 798 "parser.ml"
               : Script.script))
(* Entry script *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let script (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Script.script)
;;
# 207 "parser.mly"
  
# 825 "parser.ml"
