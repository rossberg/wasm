(*
 * (c) 2015 Andreas Rossberg
 *)

type modul
type value = Types.value

val init : Syntax.modul -> Memory.t -> modul
val invoke : modul -> int -> value list -> value list  (* raise Error *)
val eval : modul -> Syntax.expr -> value
