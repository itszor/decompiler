open Dwarfreader

let string_of_encoding = function
    DW_ATE_address -> "address"
  | DW_ATE_boolean -> "boolean"
  | DW_ATE_complex_float -> "complex float"
  | DW_ATE_float -> "float"
  | DW_ATE_signed -> "signed"
  | DW_ATE_signed_char -> "signed char"
  | DW_ATE_unsigned -> "unsigned"
  | DW_ATE_unsigned_char -> "unsigned char"
  | DW_ATE_imaginary_float -> "imaginary float"
  | DW_ATE_packed_decimal -> "packed decimal"
  | DW_ATE_numeric_string -> "numeric string"
  | DW_ATE_edited -> "edited"
  | DW_ATE_signed_fixed -> "signed fixed"
  | DW_ATE_unsigned_fixed -> "unsigned fixed"
  | DW_ATE_decimal_float -> "decimal float"
  | DW_ATE_user x -> Printf.sprintf "user encoding (%d)" x

let string_of_tag = function
    DW_TAG_array_type -> "array_type"
  | DW_TAG_class_type -> "class_type"
  | DW_TAG_entry_point -> "entry_point"
  | DW_TAG_enumeration_type -> "enumeration_type"
  | DW_TAG_formal_parameter -> "formal_parameter"
  | DW_TAG_imported_declaration -> "imported_declaration"
  | DW_TAG_label -> "label"
  | DW_TAG_lexical_block -> "lexical_block"
  | DW_TAG_member -> "member"
  | DW_TAG_pointer_type -> "pointer_type"
  | DW_TAG_reference_type -> "reference_type"
  | DW_TAG_compile_unit -> "compile_unit"
  | DW_TAG_string_type -> "string_type"
  | DW_TAG_structure_type -> "structure_type"
  | DW_TAG_subroutine_type -> "subroutine_type"
  | DW_TAG_typedef -> "typedef"
  | DW_TAG_union_type -> "union_type"
  | DW_TAG_unspecified_parameters -> "unspecified_parameters"
  | DW_TAG_variant -> "variant"
  | DW_TAG_common_block -> "common_block"
  | DW_TAG_common_inclusion -> "common_inclusion"
  | DW_TAG_inheritance -> "inheritance"
  | DW_TAG_inlined_subroutine -> "inlined_subroutine"
  | DW_TAG_module -> "module"
  | DW_TAG_ptr_to_member_type -> "ptr_to_member_type"
  | DW_TAG_set_type -> "set_type"
  | DW_TAG_subrange_type -> "subrange_type"
  | DW_TAG_with_stmt -> "with_stmt"
  | DW_TAG_access_declaration -> "access_declaration"
  | DW_TAG_base_type -> "base_type"
  | DW_TAG_catch_block -> "catch_block"
  | DW_TAG_const_type -> "const_type"
  | DW_TAG_constant -> "constant"
  | DW_TAG_enumerator -> "enumerator"
  | DW_TAG_file_type -> "file_type"
  | DW_TAG_friend -> "friend"
  | DW_TAG_namelist -> "namelist"
  | DW_TAG_namelist_item -> "namelist_item"
  | DW_TAG_packed_type -> "packed_type"
  | DW_TAG_subprogram -> "subprogram"
  | DW_TAG_template_type_parameter -> "template_type_parameter"
  | DW_TAG_template_value_parameter -> "template_value_parameter"
  | DW_TAG_thrown_type -> "thrown_type"
  | DW_TAG_try_block -> "try_block"
  | DW_TAG_variant_part -> "variant_part"
  | DW_TAG_variable -> "variable"
  | DW_TAG_volatile_type -> "volatile_type"
  | DW_TAG_dwarf_procedure -> "dwarf_procedure"
  | DW_TAG_restrict_type -> "restrict_type"
  | DW_TAG_interface_type -> "interface_type"
  | DW_TAG_namespace -> "namespace"
  | DW_TAG_imported_module -> "imported_module"
  | DW_TAG_unspecified_type -> "unspecified_type"
  | DW_TAG_partial_unit -> "partial_unit"
  | DW_TAG_imported_unit -> "imported_unit"
  | DW_TAG_condition -> "condition"
  | DW_TAG_shared_type -> "shared_type"
  | DW_TAG_lo_user -> "lo_user"
  | DW_TAG_hi_user -> "hi_user"

let is_inlined_aggregate = function
    Die_tree ((DW_TAG_structure_type, attrs), _, _)
  | Die_tree ((DW_TAG_union_type, attrs), _, _) ->
      not (attr_present attrs DW_AT_name)
  | _ -> false

let open_scope () =
  Format.printf "@[<v 2]{"

let close_scope () =
  Format.printf "@]@,}@,"

let rec print_cu_attrs attrs =
  Format.printf "@[<v>";
  Format.printf "Compilation unit: %s@," (get_attr_string attrs DW_AT_name);
  Format.printf "Build dir: %s@," (get_attr_string attrs DW_AT_comp_dir);
  Format.printf "Low PC: %lx@," (get_attr_address attrs DW_AT_low_pc);
  Format.printf "High PC: %lx@," (get_attr_address attrs DW_AT_high_pc);
  Format.printf "@]"

and print_base_type attrs =
  Format.printf "@[<v>";
  Format.printf "Base type name: %s@," (get_attr_string_opt attrs DW_AT_name);
  let enc = parse_encoding (get_attr_int attrs DW_AT_encoding) in
  Format.printf "Encoding: %s@," (string_of_encoding enc);
  Format.printf "Byte size: %ld@," (get_attr_int32 attrs DW_AT_byte_size);
  if attr_present attrs DW_AT_endianity then
    Format.printf "Endianity specified@,";
  if attr_present attrs DW_AT_bit_size
     || attr_present attrs DW_AT_bit_offset then
    Format.printf "Bit size or bit offset specified@,";
  Format.printf "@]"

and get_array_size = function
    Die_node ((DW_TAG_subrange_type, attrs), _) ->
      (get_attr_int attrs DW_AT_upper_bound) + 1
  | _ -> failwith "No array size?"

and string_of_decl typ varname hash =
  match typ with
    Die_node ((DW_TAG_base_type, attrs), _) ->
      get_attr_string attrs DW_AT_name, varname
  | Die_node ((DW_TAG_typedef, attrs), _) ->
      get_attr_string attrs DW_AT_name, varname
  | Die_node ((DW_TAG_pointer_type, attrs), _) ->
      let to_type = get_attr_deref attrs DW_AT_type hash in
      let typname, varname' = string_of_decl to_type varname hash in
      typname, "*" ^ varname'
  | Die_node ((DW_TAG_volatile_type, attrs), _) ->
      let of_type = get_attr_deref attrs DW_AT_type hash in
      let typname, varname' = string_of_decl of_type varname hash in
      Printf.sprintf "volatile %s" typname, varname'
  | Die_node ((DW_TAG_const_type, attrs), _) ->
      let of_type = get_attr_deref attrs DW_AT_type hash in
      let typname, varname' = string_of_decl of_type varname hash in
      Printf.sprintf "const %s" typname, varname'
  | Die_tree ((DW_TAG_array_type, attrs), child, _) ->
      let of_type = get_attr_deref attrs DW_AT_type hash in
      let array_size = get_array_size child in
      let typname, varname' = string_of_decl of_type varname hash in
      typname, Printf.sprintf "%s[%d]" varname' array_size
  | Die_node ((tag, attrs), _) | Die_tree ((tag, attrs), _, _) ->
      begin
        try
	  let typname = get_attr_string attrs DW_AT_name in
	  typname, varname
        with Not_found ->
	  Printf.sprintf "(??? - %s)" (string_of_tag tag), varname
      end
  | _ -> "???", varname

and print_decl typ varname hash =
  match typ with
    Die_tree ((DW_TAG_enumeration_type, attrs), children, _) ->
      begin
        try
	  let tag_name = get_attr_string attrs DW_AT_name in
	  Format.printf "enum %s %s" tag_name varname
	with Not_found ->
	  Format.printf "enum {@,";
	  print_enum_vals children;
	  Format.printf "} %s" varname
      end
  | Die_tree ((DW_TAG_structure_type, attrs), children, _) ->
      begin
        try
	  let tag_name = get_attr_string attrs DW_AT_name in
          Format.printf "struct %s %s" tag_name varname
	with Not_found ->
	  Format.printf "struct {";
	  print_aggregate_members children hash;
	  Format.printf "} %s" varname
      end
  | Die_tree ((DW_TAG_union_type, attrs), children, _) ->
      begin
        try
	  let tag_name = get_attr_string attrs DW_AT_name in
          Format.printf "union %s %s" tag_name varname
	with Not_found ->
	  Format.printf "union {";
	  print_aggregate_members children hash;
	  Format.printf "} %s" varname
      end
  | x ->
      let tname, vname = string_of_decl typ varname hash in
      Format.printf "%s %s" tname vname

and print_aggregate_type die hash =
  match die with
    Die_tree ((DW_TAG_structure_type, attrs), child, _) ->
      print_struct_type attrs child hash
  | Die_tree ((DW_TAG_union_type, attrs), child, _) ->
      print_union_type attrs child hash
  | _ -> failwith "Unexpected non-aggregate type"

and print_typedef typedef_attrs hash =
  let td_name = get_attr_string typedef_attrs DW_AT_name in
  Format.printf "@[<v>";
  begin
    try
      let td_type = get_attr_deref typedef_attrs DW_AT_type hash in
      if is_inlined_aggregate td_type then begin
	Format.printf "typedef ";
	print_aggregate_type td_type hash;
	Format.printf " %s;@," td_name
      end else begin
	Format.printf "typedef ";
	print_decl td_type td_name hash;
	Format.printf ";@,"
      end
    with Not_found ->
      (* Missing DW_AT_type seems to mean "void".  *)
      Format.printf "typedef void %s@," td_name
  end;
  Format.printf "@]"

and print_pointer_type ptr_attrs hash =
  Format.printf "@[<v>";
  Format.printf "Pointer type: ";
  let byte_size = get_attr_int32 ptr_attrs DW_AT_byte_size in
  begin
    try
      let to_type = get_attr_deref ptr_attrs DW_AT_type hash in
      let typname, varname = string_of_decl to_type "" hash in
      Format.printf "%s *%s (size = %ld)@," typname varname byte_size
    with Not_found ->
      Format.printf "void * (size = %ld)@," byte_size
  end;
  Format.printf "@]"

and print_enum_vals = function
    Die_empty -> ()
  | Die_node ((DW_TAG_enumerator, en_attrs), next) ->
      let e_name = get_attr_string en_attrs DW_AT_name
      and e_val = get_attr_int32 en_attrs DW_AT_const_value in
      Format.printf "@,%s = 0x%lx," e_name e_val;
      print_enum_vals next
  | Die_node _ -> raise (Dwarf_parse_error "non-enumerator in enum")
  | Die_tree _ -> raise (Dwarf_parse_error "unexpected tree node")

and print_enum_type enum_attrs enum_children =
  begin
    try
      let name = get_attr_string enum_attrs DW_AT_name in
      Format.printf "enum %s@,@[<v 2>{" name;
      print_enum_vals enum_children;
    with Not_found ->
      Format.printf "enum {@[<v 2>";
      print_enum_vals enum_children;
  end;
  Format.printf "@]@,};@,"

and print_aggregate_members mem hash =
  match mem with
    Die_empty -> ()
  | Die_node ((DW_TAG_member, mem_attrs), next) ->
      let mem_name = get_attr_string mem_attrs DW_AT_name
      and mem_type = get_attr_deref mem_attrs DW_AT_type hash in
      Format.printf "@,";
      print_decl mem_type mem_name hash;
      Format.printf ";";
      print_aggregate_members next hash
  | Die_node _ -> raise (Dwarf_parse_error "non-enumerator in enum")
  | Die_tree _ -> raise (Dwarf_parse_error "unexpected tree node")

and print_struct_type struct_attrs struct_children hash =
  Format.printf "@[<v 2>";
  begin
    try
      let name = get_attr_string struct_attrs DW_AT_name in
      Format.printf "struct %s {" name;
      print_aggregate_members struct_children hash;
      Format.printf "@]@,};@,"
    with Not_found ->
      Format.printf "struct {";
      print_aggregate_members struct_children hash;
      Format.printf "@]@,};@,"
  end

and print_union_type union_attrs union_children hash =
  Format.printf "@[<v 2>";
  begin
    try
      let name = get_attr_string union_attrs DW_AT_name in
      Format.printf "union %s {" name;
      print_aggregate_members union_children hash;
      Format.printf "@]@,};@,"
    with Not_found ->
      Format.printf "union {";
      print_aggregate_members union_children hash;
      Format.printf "@]@,};@,"
  end

and print_die die hash =
  match die with
    Die_node ((DW_TAG_typedef, attrs), _) ->
      print_typedef attrs hash
  | Die_node ((DW_TAG_base_type, attrs), _) ->
      print_base_type attrs
  | Die_node ((DW_TAG_pointer_type, attrs), _) ->
      print_pointer_type attrs hash
  | Die_tree ((DW_TAG_enumeration_type, attrs), child, _) ->
      print_enum_type attrs child;
  | Die_tree ((DW_TAG_structure_type, attrs), child, _) ->
      print_struct_type attrs child hash;
  | Die_tree ((DW_TAG_union_type, attrs), child, _) ->
      print_union_type attrs child hash;
  | Die_tree ((node, _), child, _) ->
      Format.printf "@[<v>";
      Format.printf "*** skipping unknown tree (%s)@," (string_of_tag node);
      Format.printf "@]";
      print_die child hash
  | Die_node ((node, _), _) ->
      Format.printf "@[<v>";
      Format.printf "*** skipping unknown node (%s)@," (string_of_tag node);
      Format.printf "@]"
  | _ -> ()

let print_all_dies die hash =
  let rec iter = function
    Die_tree (_, _, sibl) ->
      Format.printf "@[<v 0>";
      print_die die hash;
      Format.printf "@]@.";
      iter sibl
  | Die_node ((DW_TAG_compile_unit, cu_attrs), children) ->
      print_cu_attrs cu_attrs;
      iter children
  | Die_node _ ->
      Format.printf "@[<v 0>";
      print_die die hash;
      Format.printf "@]@.";
  | Die_empty -> () in
  iter die;
  Format.print_newline ()
