open Ctype
open Dwarfreader

type function_info =
  {
    args : ctype array;
    return : ctype;
    local : bool;
    prototyped : bool
  }

let function_args die die_hash =
  let rec makelist die acc argno =
    match die with
      Die_node ((DW_TAG_formal_parameter, attrs), sibl) ->
	let argname = get_attr_string attrs DW_AT_name in
	Format.printf "Arg %d, '%s':@." argno argname;
	let typeoffset = get_attr_ref attrs DW_AT_type in
	(*let die_bits' = offset_section die_bits typeoffset in*)
	let die = Hashtbl.find die_hash (Int32.to_int typeoffset) in
	let ctype = Ctype.resolve_type die die_hash in
	(* parse_die_and_children die_bits' ~abbrevs:abbrevs
          ~addr_size:cu_header.address_size ~string_sec:debug_str_sec in *)
	(*Dwarfprint.print_die die die_hash;*)
	makelist sibl (ctype :: acc) (succ argno)
    | _ -> Array.of_list acc in
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
	  Ctype.resolve_type (Hashtbl.find die_hash (Int32.to_int typeoffset))
			     die_hash
	with Not_found ->
	  C_void
      and external_p = get_attr_bool_present attrs DW_AT_external
      and prototyped = get_attr_bool_present attrs DW_AT_prototyped in
      { return = return_type;
        args = function_args child die_hash;
	local = not external_p;
	prototyped = prototyped }
  | _ -> raise Unknown_type

