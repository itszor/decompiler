open Ctype
open Dwarfreader

type function_info =
  {
    args : ctype array;
    arg_locs : location option array;
    arg_names : string array;
    framebase_loc : location option;
    return : ctype;
    local : bool;
    prototyped : bool
  }

let function_args binf die die_hash ctypes_for_cu ~compunit_baseaddr =
  let rec makelist die acc argno =
    match die with
      Die_node ((DW_TAG_formal_parameter, attrs), sibl) ->
	let argname = get_attr_string attrs DW_AT_name in
	Log.printf 3 "Arg %d, '%s':\n" argno argname;
	let typeoffset = get_attr_ref attrs DW_AT_type in
	let loc = try
	  Some (get_attr_loc attrs DW_AT_location binf.Binary_info.debug_loc
			     ~addr_size:4 ~compunit_baseaddr)
	with Not_found -> None in
	(*let die_bits' = offset_section die_bits typeoffset in*)
	let die = Hashtbl.find die_hash (Int32.to_int typeoffset) in
	let ctype = Ctype.resolve_type die die_hash ctypes_for_cu in
	(* parse_die_and_children die_bits' ~abbrevs:abbrevs
          ~addr_size:cu_header.address_size ~string_sec:debug_str_sec in *)
	(*Dwarfprint.print_die die die_hash;*)
	makelist sibl ((argname, ctype, loc) :: acc) (succ argno)
    | _ ->
        let acc' = List.rev acc in
	Array.of_list (List.map (fun (n, _, _) -> n) acc'),
	Array.of_list (List.map (fun (_, t, _) -> t) acc'),
	Array.of_list (List.map (fun (_, _, l) -> l) acc') in
  makelist die [] 0

let function_type binf name die die_hash ctypes_for_cu ~compunit_baseaddr =
  Log.printf 3 "Function '%s'\n" name;
  match die with
    Die_tree ((DW_TAG_subprogram, attrs), child, _) ->
      let return_type =
        try
	  let typeoffset = get_attr_ref attrs DW_AT_type in
	  Ctype.resolve_type (Hashtbl.find die_hash (Int32.to_int typeoffset))
			     die_hash ctypes_for_cu
	with Not_found ->
	  C_void
      and external_p = get_attr_bool_present attrs DW_AT_external
      and prototyped = get_attr_bool_present attrs DW_AT_prototyped in
      let framebase_loc =
        try
          Some (get_attr_loc attrs DW_AT_frame_base binf.Binary_info.debug_loc
			     ~addr_size:4 ~compunit_baseaddr)
	with Not_found -> None in
      let argnames, args, arglocs =
        function_args binf child die_hash ctypes_for_cu ~compunit_baseaddr in
      { return = return_type;
        args = args;
	arg_locs = arglocs;
	arg_names = argnames;
	framebase_loc = framebase_loc;
	local = not external_p;
	prototyped = prototyped }
  | Die_node ((DW_TAG_subprogram, attrs), _) ->
      let return_type =
        try
	  let typeoffset = get_attr_ref attrs DW_AT_type in
	  Ctype.resolve_type (Hashtbl.find die_hash (Int32.to_int typeoffset))
			     die_hash ctypes_for_cu
	with Not_found ->
	  C_void
      and external_p = get_attr_bool_present attrs DW_AT_external
      and prototyped = get_attr_bool_present attrs DW_AT_prototyped in
      let framebase_loc =
        try
          Some (get_attr_loc attrs DW_AT_frame_base binf.Binary_info.debug_loc
			     ~addr_size:4 ~compunit_baseaddr)
	with Not_found -> None in
      { return = return_type;
        args = [| |];
	arg_locs = [| |];
	arg_names = [| |];
	framebase_loc = framebase_loc;
	local = not external_p;
	prototyped = prototyped }
  | _ -> raise Unknown_type

type var =
  {
    var_name : string;
    var_type : Ctype.ctype;
    var_size : int;
    var_location : Dwarfreader.location option
  }

let function_vars die die_hash locbits ~compunit_baseaddr ctypes_for_cu =
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
	let var_type = Ctype.resolve_type type_die die_hash ctypes_for_cu in
	let type_size = Ctype.dwarf_type_size type_die die_hash in
	let var = {
	  var_name = var_name;
	  var_type = var_type;
	  var_size = type_size;
	  var_location = var_loc
	} in
	makelist sibl (var :: acc)
    | Die_tree ((DW_TAG_lexical_block, attrs), child, _) ->
        (* FIXME: this is sketchy! Match up genuine lexical blocks to basic
	   blocks, and handle nested declarations properly.  *)
        Log.printf 3 "lexical block within function\n";
	makelist child acc
    | _ -> acc in
  match die with
    Die_tree ((DW_TAG_subprogram, attrs), child, _) ->
      makelist child []
  | _ -> []
