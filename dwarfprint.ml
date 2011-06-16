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

let rec print_cu attrs children =
  Printf.printf "Compilation unit: %s\n" (get_attr_string attrs DW_AT_name);
  Printf.printf "Build dir: %s\n" (get_attr_string attrs DW_AT_comp_dir);
  Printf.printf "Low PC: %lx\n" (get_attr_address attrs DW_AT_low_pc);
  Printf.printf "High PC: %lx\n" (get_attr_address attrs DW_AT_high_pc);
  print_die children

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

and print_die = function
    Die_node ((DW_TAG_compile_unit, cu_attrs), children) ->
      print_cu cu_attrs children
  | Die_node ((DW_TAG_typedef, attrs), children) ->
      print_typedef attrs;
      print_die children
  | Die_node ((DW_TAG_base_type, attrs), children) ->
      print_base_type attrs;
      print_die children
  | Die_tree (node, child, sibl) ->
      Printf.printf "*** skipping unknown tree\n";
      print_die child; print_die sibl
  | Die_node (_, x) ->
      Printf.printf "*** skipping unknown node\n";
      print_die x
  | _ -> ()
