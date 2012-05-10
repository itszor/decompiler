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

exception Unresolved_type of (dwarf_tag
			     * ((dwarf_attribute * attr_datum) list)) die

let rec resolve_type die die_hash =
  let rec build = function
    Die_node ((DW_TAG_typedef, attrs), _) ->
      let targ = get_attr_deref attrs DW_AT_type die_hash in
      build targ
  | Die_node ((DW_TAG_pointer_type, attrs), _) ->
      let targ = get_attr_deref attrs DW_AT_type die_hash in
      C_pointer (fun () -> build targ)
  | Die_tree ((DW_TAG_structure_type, attrs), child, _) ->
      C_struct (resolve_aggregate child die_hash)
  | Die_tree ((DW_TAG_union_type, attrs), child, _) ->
      C_union (resolve_aggregate child die_hash)
  | Die_tree ((DW_TAG_enumeration_type, attrs), _, _) ->
      C_enum
  | Die_node ((DW_TAG_base_type, attrs), _) as die' ->
      let enc = parse_encoding (get_attr_int attrs DW_AT_encoding)
      and size = get_attr_int attrs DW_AT_byte_size in
      begin match enc, size with
        DW_ATE_signed, 4 -> C_int
      | DW_ATE_unsigned, 4 -> C_unsigned C_int
      | DW_ATE_signed, 2 -> C_short
      | DW_ATE_unsigned, 2 -> C_unsigned C_short
      | (DW_ATE_signed | DW_ATE_signed_char), 1 -> C_signed C_char
      | (DW_ATE_unsigned | DW_ATE_unsigned_char), 1 -> C_unsigned C_char
      | DW_ATE_float, 4 -> C_float
      | DW_ATE_float, 8 -> C_double
      | _ -> raise (Unresolved_type die')
      end
  | Die_tree ((DW_TAG_array_type, _), child, _) as die' ->
      begin match child with
        Die_node ((DW_TAG_subrange_type, attrs), _) ->
	  let upper_bound = get_attr_int attrs DW_AT_upper_bound in
	  let elem_type = get_attr_deref attrs DW_AT_type die_hash in
	  let typ = resolve_type elem_type die_hash in
	  C_array (upper_bound, typ)
      | _ -> raise (Unresolved_type die')
      end
  | die' -> raise (Unresolved_type die') in
  build die
  
and resolve_aggregate die die_hash =
  let rec build = function
    Die_empty -> []
  | Die_node ((DW_TAG_member, mem_attrs), next) ->
      let mem_name = get_attr_string mem_attrs DW_AT_name
      and mem_type = get_attr_deref mem_attrs DW_AT_type die_hash in
      let resolved_type = resolve_type mem_type die_hash in
      { name = mem_name; typ = resolved_type } :: build next
  | _ -> raise Unknown_type in
  build die

