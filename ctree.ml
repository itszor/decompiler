(* Tree representation of program elements.  *)

type c_elem =
    Declaration of Ctype.ctype * string
  | Function of Function.function_info
  
type c_expr =
  unit
