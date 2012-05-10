(* This is (so far) a really bad approximation of the C type system!  *)

type ctype =
    C_void
  | C_int
  | C_short
  | C_char
  | C_float
  | C_double
  | C_signed of ctype
  | C_unsigned of ctype
  | C_pointer of (unit -> ctype)
  | C_const of ctype
  | C_volatile of ctype
  | C_struct of aggregate_member list
  | C_union of aggregate_member list
  | C_array of int * ctype
  | C_enum (* of ... *)

and aggregate_member = {
  name : string;
  typ : ctype
}

exception Unknown_type

let base_type_from_debug_info = ()
