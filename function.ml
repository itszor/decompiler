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
  Format.printf "Function '%s'@." name;
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

let function_frame_base die die_hash locbits ~compunit_baseaddr =
  match die with
    Die_tree ((DW_TAG_subprogram, attrs), _, _) ->
      let framebase = get_attr_loc attrs DW_AT_frame_base locbits
				   ~addr_size:4 ~compunit_baseaddr in
      framebase
  | _ -> failwith "not subprogram die"

type var =
  {
    var_name : string;
    var_type : Ctype.ctype;
    var_size : int;
    var_location : Dwarfreader.location option
  }

let function_vars die die_hash locbits ~compunit_baseaddr =
  let rec makelist die acc =
    match die with
      Die_node ((DW_TAG_formal_parameter, _), sibl) ->
        (* Skip over formal parameters...  *)
        makelist sibl acc
    | Die_node ((DW_TAG_variable, attrs), sibl) ->
        let var_name = get_attr_string attrs DW_AT_name
	and type_offset = get_attr_ref attrs DW_AT_type in
	let var_loc =
	  try
	    Some (get_attr_loc attrs DW_AT_location locbits ~addr_size:4
					 ~compunit_baseaddr)
	  with Not_found -> None in
	let type_die = Hashtbl.find die_hash (Int32.to_int type_offset) in
	let var_type = Ctype.resolve_type type_die die_hash in
	let type_size = Ctype.dwarf_type_size type_die die_hash in
	let var = {
	  var_name = var_name;
	  var_type = var_type;
	  var_size = type_size;
	  var_location = var_loc
	} in
	makelist sibl (var :: acc)
    | _ -> acc in
  match die with
    Die_tree ((DW_TAG_subprogram, attrs), child, _) ->
      makelist child []
  | _ -> []
