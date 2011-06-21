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

let rec print_cu attrs children hash =
  Printf.printf "Compilation unit: %s\n" (get_attr_string attrs DW_AT_name);
  Printf.printf "Build dir: %s\n" (get_attr_string attrs DW_AT_comp_dir);
  Printf.printf "Low PC: %lx\n" (get_attr_address attrs DW_AT_low_pc);
  Printf.printf "High PC: %lx\n" (get_attr_address attrs DW_AT_high_pc);
  print_die children hash

and print_base_type attrs =
  Printf.printf "Base type name: %s\n" (get_attr_string_opt attrs DW_AT_name);
  let enc = parse_encoding (get_attr_int attrs DW_AT_encoding) in
  Printf.printf "Encoding: %s\n" (string_of_encoding enc);
  Printf.printf "Byte size: %ld\n" (get_attr_int32 attrs DW_AT_byte_size);
  if attr_present attrs DW_AT_endianity then
    Printf.printf "Endianity specified\n";
  if attr_present attrs DW_AT_bit_size
     || attr_present attrs DW_AT_bit_offset then
    Printf.printf "Bit size or bit offset specified\n";
  Printf.printf "--\n"

and print_typedef typedef_attrs =
  let td_name = get_attr_string typedef_attrs DW_AT_name in
  try
    let td_type = get_attr_ref typedef_attrs DW_AT_type in
    Printf.printf "typedef <%ld> %s\n" td_type td_name
  with Not_found ->
    (* Missing DW_AT_type seems to mean "void".  *)
    Printf.printf "typedef void %s\n" td_name

and print_enum enum_attrs enum_inf =
  begin match enum_inf with
    Die_node ((DW_TAG_enumerator, attrs), rest) ->
      let tag_name = get_attr_string attrs DW_AT_name
      and enumerator_value = get_attr_int32 attrs DW_AT_const_value in
      Printf.printf "  %s = 0x%lx,\n" tag_name enumerator_value;
      print_enum enum_attrs rest
  | _ -> ()
  end

and print_pointer_type ptr_attrs =
  Printf.printf "Pointer type: ";
  let byte_size = get_attr_int32 ptr_attrs DW_AT_byte_size in
  try
    let to_type = get_attr_ref ptr_attrs DW_AT_type in
    Printf.printf "<%ld> * (size = %ld)\n" to_type byte_size
  with Not_found ->
    Printf.printf "void * (size = %ld)\n" byte_size

and print_enum_vals = function
    Die_empty -> ()
  | Die_node ((DW_TAG_enumerator, en_attrs), next) ->
      let e_name = get_attr_string en_attrs DW_AT_name
      and e_val = get_attr_int32 en_attrs DW_AT_const_value in
      Printf.printf "  %s = 0x%lx,\n" e_name e_val;
      print_enum_vals next
  | Die_node _ -> raise (Dwarf_parse_error "non-enumerator in enum")
  | Die_tree _ -> raise (Dwarf_parse_error "unexpected tree node")

and print_enum_type enum_attrs enum_children =
  try
    let name = get_attr_string enum_attrs DW_AT_name in
    Printf.printf "enum %s {\n" name;
    print_enum_vals enum_children;
    Printf.printf "}\n"
  with Not_found ->
    Printf.printf "enum {\n";
    print_enum_vals enum_children;
    Printf.printf "}\n"

and print_struct_members = function
    Die_empty -> ()
  | Die_node ((DW_TAG_member, mem_attrs), next) ->
      let mem_name = get_attr_string mem_attrs DW_AT_name
      and mem_type = get_attr_ref mem_attrs DW_AT_type in
      Printf.printf "  <%ld> %s;\n" mem_type mem_name;
      print_struct_members next
  | Die_node _ -> raise (Dwarf_parse_error "non-enumerator in enum")
  | Die_tree _ -> raise (Dwarf_parse_error "unexpected tree node")

and print_struct_type struct_attrs struct_children =
  try
    let name = get_attr_string struct_attrs DW_AT_name in
    Printf.printf "struct %s {\n" name;
    print_struct_members struct_children;
    Printf.printf "}\n"
  with Not_found ->
    Printf.printf "struct {\n";
    print_struct_members struct_children;
    Printf.printf "}\n"

and print_die die hash =
  match die with
    Die_node ((DW_TAG_compile_unit, cu_attrs), children) ->
      print_cu cu_attrs children hash
  | Die_node ((DW_TAG_typedef, attrs), children) ->
      print_typedef attrs;
      print_die children hash
  | Die_node ((DW_TAG_base_type, attrs), children) ->
      print_base_type attrs;
      print_die children hash
  | Die_node ((DW_TAG_pointer_type, attrs), sibl) ->
      print_pointer_type attrs;
      print_die sibl hash
  | Die_tree ((DW_TAG_enumeration_type, attrs), child, sibl) ->
      print_enum_type attrs child;
      print_die sibl hash
  | Die_tree ((DW_TAG_structure_type, attrs), child, sibl) ->
      print_struct_type attrs child;
      print_die sibl hash
  | Die_tree ((node, _), child, sibl) ->
      Printf.printf "*** skipping unknown tree (%s)\n" (string_of_tag node);
      print_die child hash; print_die sibl hash
  | Die_node ((node, _), x) ->
      Printf.printf "*** skipping unknown node (%s)\n" (string_of_tag node);
      print_die x hash
  | _ -> ()
