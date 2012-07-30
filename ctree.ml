(* Tree representation of program elements.  Uses AST from FrontC.  *)

open Cabs

let convert_basetype ctyp =
  let rec convert = function
    Ctype.C_void -> VOID
  | Ctype.C_longlong -> INT (LONG_LONG, SIGNED)
  | Ctype.C_int
  | Ctype.C_signed Ctype.C_int -> INT (NO_SIZE, SIGNED)
  | Ctype.C_unsigned Ctype.C_int -> INT (NO_SIZE, UNSIGNED)
  | Ctype.C_short
  | Ctype.C_signed Ctype.C_short -> INT (SHORT, SIGNED)
  | Ctype.C_char
  | Ctype.C_unsigned Ctype.C_char -> CHAR UNSIGNED
  | Ctype.C_signed Ctype.C_char -> CHAR SIGNED
  | Ctype.C_float -> FLOAT false
  | Ctype.C_double -> DOUBLE false
  | Ctype.C_pointer targ -> PTR (convert targ)
  | Ctype.C_const targ -> CONST (convert targ)
  | Ctype.C_volatile targ -> VOLATILE (convert targ)
  | Ctype.C_struct (nm, aglist) -> convert_struct nm aglist
  | Ctype.C_union (nm, aglist) -> convert_union nm aglist
  | Ctype.C_enum -> ENUM ("", [])
  | Ctype.C_typedef nm -> (* ?? *) NAMED_TYPE nm
  | Ctype.C_typetag nm -> (* ?? *) NAMED_TYPE nm
  | Ctype.C_array (bound, typ) ->
      ARRAY (convert typ, CONSTANT (CONST_INT (string_of_int bound)))
  | Ctype.C_funtype _ -> failwith "convert_basetype/funtype"
  | _ -> failwith "convert_basetype"
  and convert_struct nm aglist =
    STRUCT (nm, List.map convert_namegroup aglist)
  and convert_union nm aglist =
    UNION (nm, List.map convert_namegroup aglist)
  and convert_namegroup aggr_mem =
    let base_type = convert aggr_mem.Ctype.typ
    and storage = (* ?? *) NO_STORAGE in
    let name = aggr_mem.Ctype.name, base_type, [], NOTHING in
    base_type, storage, [name] in
  convert ctyp

let convert_function fname ftype blk_arr =
  let return_type = convert_basetype ftype.Function.return in
  let args = ref [] in
  let nargs = Array.length ftype.Function.args in
  for i = nargs - 1 downto 0 do
    let base_type = convert_basetype ftype.Function.args.(i) in
    let arg_name = ftype.Function.arg_names.(i), base_type, [], NOTHING in
    let arg_sname = base_type, NO_STORAGE, arg_name in
    args := arg_sname :: !args
  done;
  let proto = return_type, !args, false in
  let return_name = fname, PROTO proto, [], NOTHING in
  let return_singlename = return_type, NO_STORAGE, return_name in
  let body = [], NOP in
  FUNDEF (return_singlename, body)
  
let convert_typedef typename dtype =
  let basetype = convert_basetype dtype in
  let name = typename, basetype, [], NOTHING in
  let namegroup = basetype, NO_STORAGE, [name] in 
  TYPEDEF namegroup
