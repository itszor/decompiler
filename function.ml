open Ctype
open Dwarfreader

type function_info =
  {
    args : ctype array;
    return : ctype
  }

let type_for_function name =
  match name with
    "foo" ->
      { args = [| C_int; C_int; C_int; C_int; C_int; C_int |];
        return = C_int }
  | "blah" ->
      { args = [| C_int; C_int |];
        return = C_int }
  | "blah2" ->
      { args = [| C_pointer (fun () -> C_int) |];
        return = C_int }
  | "main" ->
      { args = [| |];
        return = C_int }
  | "loop" ->
      { args = [| C_int |];
        return = C_int }
  | _ -> raise Not_found

let function_args die die_hash =
  let rec makelist die acc argno =
    match die with
      Die_node ((DW_TAG_formal_parameter, attrs), sibl) ->
	let argname = get_attr_string attrs DW_AT_name in
	Format.printf "Arg %d, '%s':@." argno argname;
	let typeoffset = get_attr_ref attrs DW_AT_type in
	(*let die_bits' = offset_section die_bits typeoffset in*)
	let die = Hashtbl.find die_hash (Int32.to_int typeoffset) in
	(* parse_die_and_children die_bits' ~abbrevs:abbrevs
          ~addr_size:cu_header.address_size ~string_sec:debug_str_sec in *)
	(*Dwarfprint.print_die die die_hash;*)
	makelist sibl (die :: acc) (succ argno)
    | _ -> acc in
  makelist die [] 0

let function_type name die die_hash =
  (*Format.printf "Function '%s'@." name;*)
  match die with
    Die_tree ((DW_TAG_subprogram, attrs), child, _) ->
      let return_type =
        try
	  let typeoffset = get_attr_ref attrs DW_AT_type in
	  (*Format.printf "It's a subprogram (type=%ld).@."
	    typeoffset;*)
	  Some (Hashtbl.find die_hash (Int32.to_int typeoffset))
	with Not_found ->
	  None in
      return_type, function_args child die_hash
  | _ -> raise Unknown_type

