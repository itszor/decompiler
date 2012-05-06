(* This is (so far) a really bad approximation of the C type system!  *)

type ctype =
    C_void
  | C_int
  | C_short
  | C_char
  | C_signed of ctype
  | C_unsigned of ctype
  | C_pointer of ctype
  | C_const of ctype
  | C_volatile of ctype
