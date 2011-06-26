exception Dwarf_parse_error of string

(* Ocaml 3.11.x doesn't have shift_left_big_int!  *)

let lshift_7 big_int =
  (* Big_int.shift_left_big_int big_int 7 *)
  Big_int.mult_int_big_int 128 big_int

(* Parse ULEB128 value in DWBITS to a Big_int.  *)

let parse_uleb128 dwbits =
  let rec build bits =
    bitmatch bits with
      { false : 1 : littleendian;
        chunk : 7 : littleendian;
	rest : -1 : bitstring } ->
	  Big_int.big_int_of_int chunk, rest
    | { true : 1 : littleendian;
        chunk : 7 : littleendian;
	rest : -1 : bitstring } ->
	  let higher_bits, rest' = build rest in
	  Big_int.add_int_big_int chunk (lshift_7 higher_bits), rest'
    | { _ } -> raise (Dwarf_parse_error "uleb128") in
  build dwbits

let signed_value x =
  if x < 64 then x else x - 128

(* Parse SLEB128 value in DWBITS to a Big_int.  *)

let parse_sleb128 dwbits =
  let rec build bits =
    bitmatch bits with
      { false : 1 : littleendian;
        chunk : 7 : littleendian;
	rest : -1 : bitstring } ->
	  Big_int.big_int_of_int (signed_value chunk), rest
    | { true : 1 : littleendian;
	chunk : 7 : littleendian;
	rest : -1 : bitstring } ->
	  let higher_bits, rest' = build rest in
	  Big_int.add_int_big_int (signed_value chunk)
	    (lshift_7 higher_bits), rest'
    | { _ } -> raise (Dwarf_parse_error "sleb128") in
  build dwbits

let parse_uleb128_int dwbits =
  let x, dwbits = parse_uleb128 dwbits in
  if not (Big_int.is_int_big_int x) then
    failwith "uleb128 value too big";
  Big_int.int_of_big_int x, dwbits

let parse_sleb128_int dwbits =
  let x, dwbits = parse_sleb128 dwbits in
  if not (Big_int.is_int_big_int x) then
    failwith "uleb128 value too big";
  Big_int.int_of_big_int x, dwbits

type dwarf_tag =
    DW_TAG_array_type
  | DW_TAG_class_type
  | DW_TAG_entry_point
  | DW_TAG_enumeration_type
  | DW_TAG_formal_parameter
  | DW_TAG_imported_declaration
  | DW_TAG_label
  | DW_TAG_lexical_block
  | DW_TAG_member
  | DW_TAG_pointer_type
  | DW_TAG_reference_type
  | DW_TAG_compile_unit
  | DW_TAG_string_type
  | DW_TAG_structure_type
  | DW_TAG_subroutine_type
  | DW_TAG_typedef
  | DW_TAG_union_type
  | DW_TAG_unspecified_parameters
  | DW_TAG_variant
  | DW_TAG_common_block
  | DW_TAG_common_inclusion
  | DW_TAG_inheritance
  | DW_TAG_inlined_subroutine
  | DW_TAG_module
  | DW_TAG_ptr_to_member_type
  | DW_TAG_set_type
  | DW_TAG_subrange_type
  | DW_TAG_with_stmt
  | DW_TAG_access_declaration
  | DW_TAG_base_type
  | DW_TAG_catch_block
  | DW_TAG_const_type
  | DW_TAG_constant
  | DW_TAG_enumerator
  | DW_TAG_file_type
  | DW_TAG_friend
  | DW_TAG_namelist
  | DW_TAG_namelist_item
  | DW_TAG_packed_type
  | DW_TAG_subprogram
  | DW_TAG_template_type_parameter
  | DW_TAG_template_value_parameter
  | DW_TAG_thrown_type
  | DW_TAG_try_block
  | DW_TAG_variant_part
  | DW_TAG_variable
  | DW_TAG_volatile_type
  | DW_TAG_dwarf_procedure
  | DW_TAG_restrict_type
  | DW_TAG_interface_type
  | DW_TAG_namespace
  | DW_TAG_imported_module
  | DW_TAG_unspecified_type
  | DW_TAG_partial_unit
  | DW_TAG_imported_unit
  | DW_TAG_condition
  | DW_TAG_shared_type
  | DW_TAG_lo_user
  | DW_TAG_hi_user

let parse_tag = function
    0x01 -> DW_TAG_array_type
  | 0x02 -> DW_TAG_class_type
  | 0x03 -> DW_TAG_entry_point
  | 0x04 -> DW_TAG_enumeration_type
  | 0x05 -> DW_TAG_formal_parameter
  | 0x08 -> DW_TAG_imported_declaration
  | 0x0a -> DW_TAG_label
  | 0x0b -> DW_TAG_lexical_block
  | 0x0d -> DW_TAG_member
  | 0x0f -> DW_TAG_pointer_type
  | 0x10 -> DW_TAG_reference_type
  | 0x11 -> DW_TAG_compile_unit
  | 0x12 -> DW_TAG_string_type
  | 0x13 -> DW_TAG_structure_type
  | 0x15 -> DW_TAG_subroutine_type
  | 0x16 -> DW_TAG_typedef
  | 0x17 -> DW_TAG_union_type
  | 0x18 -> DW_TAG_unspecified_parameters
  | 0x19 -> DW_TAG_variant
  | 0x1a -> DW_TAG_common_block
  | 0x1b -> DW_TAG_common_inclusion
  | 0x1c -> DW_TAG_inheritance
  | 0x1d -> DW_TAG_inlined_subroutine
  | 0x1e -> DW_TAG_module
  | 0x1f -> DW_TAG_ptr_to_member_type
  | 0x20 -> DW_TAG_set_type
  | 0x21 -> DW_TAG_subrange_type
  | 0x22 -> DW_TAG_with_stmt
  | 0x23 -> DW_TAG_access_declaration
  | 0x24 -> DW_TAG_base_type
  | 0x25 -> DW_TAG_catch_block
  | 0x26 -> DW_TAG_const_type
  | 0x27 -> DW_TAG_constant
  | 0x28 -> DW_TAG_enumerator
  | 0x29 -> DW_TAG_file_type
  | 0x2a -> DW_TAG_friend
  | 0x2b -> DW_TAG_namelist
  | 0x2c -> DW_TAG_namelist_item
  | 0x2d -> DW_TAG_packed_type
  | 0x2e -> DW_TAG_subprogram
  | 0x2f -> DW_TAG_template_type_parameter
  | 0x30 -> DW_TAG_template_value_parameter
  | 0x31 -> DW_TAG_thrown_type
  | 0x32 -> DW_TAG_try_block
  | 0x33 -> DW_TAG_variant_part
  | 0x34 -> DW_TAG_variable
  | 0x35 -> DW_TAG_volatile_type
  | 0x36 -> DW_TAG_dwarf_procedure
  | 0x37 -> DW_TAG_restrict_type
  | 0x38 -> DW_TAG_interface_type
  | 0x39 -> DW_TAG_namespace
  | 0x3a -> DW_TAG_imported_module
  | 0x3b -> DW_TAG_unspecified_type
  | 0x3c -> DW_TAG_partial_unit
  | 0x3d -> DW_TAG_imported_unit
  | 0x3f -> DW_TAG_condition
  | 0x40 -> DW_TAG_shared_type
  | 0x4080 -> DW_TAG_lo_user
  | 0xffff -> DW_TAG_hi_user
  | _ -> raise (Dwarf_parse_error "parse_tag")

let parse_child_determination dwbits =
  bitmatch dwbits with
    { 0x00 : 8 : littleendian; rest : -1 : bitstring } -> false, rest
  | { 0x01 : 8 : littleendian; rest : -1 : bitstring } -> true, rest
  | { _ } -> raise (Dwarf_parse_error "parse_child_determination")

type dwarf_attribute =
    DW_AT_sibling
  | DW_AT_location
  | DW_AT_name
  | DW_AT_ordering
  | DW_AT_byte_size
  | DW_AT_bit_offset
  | DW_AT_bit_size
  | DW_AT_stmt_list
  | DW_AT_low_pc
  | DW_AT_high_pc
  | DW_AT_language
  | DW_AT_discr
  | DW_AT_discr_value
  | DW_AT_visibility
  | DW_AT_import
  | DW_AT_string_length
  | DW_AT_common_reference
  | DW_AT_comp_dir
  | DW_AT_const_value
  | DW_AT_containing_type
  | DW_AT_default_value
  | DW_AT_inline
  | DW_AT_is_optional
  | DW_AT_lower_bound
  | DW_AT_producer
  | DW_AT_prototyped
  | DW_AT_return_addr
  | DW_AT_start_scope
  | DW_AT_bit_stride
  | DW_AT_upper_bound
  | DW_AT_abstract_origin
  | DW_AT_accessibility
  | DW_AT_address_class
  | DW_AT_artificial
  | DW_AT_base_types
  | DW_AT_calling_convention
  | DW_AT_count
  | DW_AT_data_member_location
  | DW_AT_decl_column
  | DW_AT_decl_file
  | DW_AT_decl_line
  | DW_AT_declaration
  | DW_AT_discr_list
  | DW_AT_encoding
  | DW_AT_external
  | DW_AT_frame_base
  | DW_AT_friend
  | DW_AT_identifier_case
  | DW_AT_macro_info
  | DW_AT_namelist_item
  | DW_AT_priority
  | DW_AT_segment
  | DW_AT_specification
  | DW_AT_static_link
  | DW_AT_type
  | DW_AT_use_location
  | DW_AT_variable_parameter
  | DW_AT_virtuality
  | DW_AT_vtable_elem_location
  | DW_AT_allocated
  | DW_AT_associated
  | DW_AT_data_location
  | DW_AT_byte_stride
  | DW_AT_entry_pc
  | DW_AT_use_UTF8
  | DW_AT_extension
  | DW_AT_ranges
  | DW_AT_trampoline
  | DW_AT_call_column
  | DW_AT_call_file
  | DW_AT_call_line
  | DW_AT_description
  | DW_AT_binary_scale
  | DW_AT_decimal_scale
  | DW_AT_small
  | DW_AT_decimal_sign
  | DW_AT_digit_count
  | DW_AT_picture_string
  | DW_AT_mutable
  | DW_AT_threads_scaled
  | DW_AT_explicit
  | DW_AT_object_pointer
  | DW_AT_endianity
  | DW_AT_elemental
  | DW_AT_pure
  | DW_AT_recursive
  | DW_AT_lo_user
  | DW_AT_hi_user

let parse_attribute = function
    0x01 -> DW_AT_sibling
  | 0x02 -> DW_AT_location
  | 0x03 -> DW_AT_name
  | 0x09 -> DW_AT_ordering
  | 0x0b -> DW_AT_byte_size
  | 0x0c -> DW_AT_bit_offset
  | 0x0d -> DW_AT_bit_size
  | 0x10 -> DW_AT_stmt_list
  | 0x11 -> DW_AT_low_pc
  | 0x12 -> DW_AT_high_pc
  | 0x13 -> DW_AT_language
  | 0x15 -> DW_AT_discr
  | 0x16 -> DW_AT_discr_value
  | 0x17 -> DW_AT_visibility
  | 0x18 -> DW_AT_import
  | 0x19 -> DW_AT_string_length
  | 0x1a -> DW_AT_common_reference
  | 0x1b -> DW_AT_comp_dir
  | 0x1c -> DW_AT_const_value
  | 0x1d -> DW_AT_containing_type
  | 0x1e -> DW_AT_default_value
  | 0x20 -> DW_AT_inline
  | 0x21 -> DW_AT_is_optional
  | 0x22 -> DW_AT_lower_bound
  | 0x25 -> DW_AT_producer
  | 0x27 -> DW_AT_prototyped
  | 0x2a -> DW_AT_return_addr
  | 0x2c -> DW_AT_start_scope
  | 0x2e -> DW_AT_bit_stride
  | 0x2f -> DW_AT_upper_bound
  | 0x31 -> DW_AT_abstract_origin
  | 0x32 -> DW_AT_accessibility
  | 0x33 -> DW_AT_address_class
  | 0x34 -> DW_AT_artificial
  | 0x35 -> DW_AT_base_types
  | 0x36 -> DW_AT_calling_convention
  | 0x37 -> DW_AT_count
  | 0x38 -> DW_AT_data_member_location
  | 0x39 -> DW_AT_decl_column
  | 0x3a -> DW_AT_decl_file
  | 0x3b -> DW_AT_decl_line
  | 0x3c -> DW_AT_declaration
  | 0x3d -> DW_AT_discr_list
  | 0x3e -> DW_AT_encoding
  | 0x3f -> DW_AT_external
  | 0x40 -> DW_AT_frame_base
  | 0x41 -> DW_AT_friend
  | 0x42 -> DW_AT_identifier_case
  | 0x43 -> DW_AT_macro_info
  | 0x44 -> DW_AT_namelist_item
  | 0x45 -> DW_AT_priority
  | 0x46 -> DW_AT_segment
  | 0x47 -> DW_AT_specification
  | 0x48 -> DW_AT_static_link
  | 0x49 -> DW_AT_type
  | 0x4a -> DW_AT_use_location
  | 0x4b -> DW_AT_variable_parameter
  | 0x4c -> DW_AT_virtuality
  | 0x4d -> DW_AT_vtable_elem_location
  | 0x4e -> DW_AT_allocated
  | 0x4f -> DW_AT_associated
  | 0x50 -> DW_AT_data_location
  | 0x51 -> DW_AT_byte_stride
  | 0x52 -> DW_AT_entry_pc
  | 0x53 -> DW_AT_use_UTF8
  | 0x54 -> DW_AT_extension
  | 0x55 -> DW_AT_ranges
  | 0x56 -> DW_AT_trampoline
  | 0x57 -> DW_AT_call_column
  | 0x58 -> DW_AT_call_file
  | 0x59 -> DW_AT_call_line
  | 0x5a -> DW_AT_description
  | 0x5b -> DW_AT_binary_scale
  | 0x5c -> DW_AT_decimal_scale
  | 0x5d -> DW_AT_small
  | 0x5e -> DW_AT_decimal_sign
  | 0x5f -> DW_AT_digit_count
  | 0x60 -> DW_AT_picture_string
  | 0x61 -> DW_AT_mutable
  | 0x62 -> DW_AT_threads_scaled
  | 0x63 -> DW_AT_explicit
  | 0x64 -> DW_AT_object_pointer
  | 0x65 -> DW_AT_endianity
  | 0x66 -> DW_AT_elemental
  | 0x67 -> DW_AT_pure
  | 0x68 -> DW_AT_recursive
  | 0x2000 -> DW_AT_lo_user
  | 0x3fff -> DW_AT_hi_user
  | _ -> raise (Dwarf_parse_error "parse_attribute")

type dwarf_form =
    DW_FORM_addr
  | DW_FORM_block
  | DW_FORM_block1
  | DW_FORM_block2
  | DW_FORM_block4
  | DW_FORM_data1
  | DW_FORM_data2
  | DW_FORM_data4
  | DW_FORM_data8
  | DW_FORM_sdata
  | DW_FORM_udata
  | DW_FORM_string
  | DW_FORM_strp
  | DW_FORM_flag
  | DW_FORM_ref_addr
  | DW_FORM_ref1
  | DW_FORM_ref2
  | DW_FORM_ref4
  | DW_FORM_ref8
  | DW_FORM_ref_udata
  | DW_FORM_indirect

let parse_attribute_form = function
    0x01 -> DW_FORM_addr
  | 0x03 -> DW_FORM_block2
  | 0x04 -> DW_FORM_block4
  | 0x05 -> DW_FORM_data2
  | 0x06 -> DW_FORM_data4
  | 0x07 -> DW_FORM_data8
  | 0x08 -> DW_FORM_string
  | 0x09 -> DW_FORM_block
  | 0x0a -> DW_FORM_block1
  | 0x0b -> DW_FORM_data1
  | 0x0c -> DW_FORM_flag
  | 0x0d -> DW_FORM_sdata
  | 0x0e -> DW_FORM_strp
  | 0x0f -> DW_FORM_udata
  | 0x10 -> DW_FORM_ref_addr
  | 0x11 -> DW_FORM_ref1
  | 0x12 -> DW_FORM_ref2
  | 0x13 -> DW_FORM_ref4
  | 0x14 -> DW_FORM_ref8
  | 0x15 -> DW_FORM_ref_udata
  | 0x16 -> DW_FORM_indirect
  | _ -> raise (Dwarf_parse_error "parse_attribute_form")

type dwarf_base_type_encoding =
    DW_ATE_address
  | DW_ATE_boolean
  | DW_ATE_complex_float
  | DW_ATE_float
  | DW_ATE_signed
  | DW_ATE_signed_char
  | DW_ATE_unsigned
  | DW_ATE_unsigned_char
  | DW_ATE_imaginary_float
  | DW_ATE_packed_decimal
  | DW_ATE_numeric_string
  | DW_ATE_edited
  | DW_ATE_signed_fixed
  | DW_ATE_unsigned_fixed
  | DW_ATE_decimal_float
  | DW_ATE_user of int

let parse_encoding = function
    0x01 -> DW_ATE_address
  | 0x02 -> DW_ATE_boolean
  | 0x03 -> DW_ATE_complex_float
  | 0x04 -> DW_ATE_float
  | 0x05 -> DW_ATE_signed
  | 0x06 -> DW_ATE_signed_char
  | 0x07 -> DW_ATE_unsigned
  | 0x08 -> DW_ATE_unsigned_char
  | 0x09 -> DW_ATE_imaginary_float
  | 0x0a -> DW_ATE_packed_decimal
  | 0x0b -> DW_ATE_numeric_string
  | 0x0c -> DW_ATE_edited
  | 0x0d -> DW_ATE_signed_fixed
  | 0x0e -> DW_ATE_unsigned_fixed
  | 0x0f -> DW_ATE_decimal_float
  | x when x >= 0x80 && x <= 0xff -> DW_ATE_user (x - 0x80)
  | _ -> raise (Dwarf_parse_error "parse_encoding")

type dwarf_abbrev =
  {
    abv_num : int;
    abv_tag : dwarf_tag;
    abv_attribs : (dwarf_attribute * dwarf_form) list;
    abv_has_children : bool
  }

(* Parse a single abbreviation.  *)

let parse_one_abbrev dwbits =
  let num, dwbits = parse_uleb128_int dwbits in
  if num = 0 then
    None, dwbits
  else begin
    let tag_code, dwbits = parse_uleb128_int dwbits in
    let tag = parse_tag tag_code
    and has_children, dwbits = parse_child_determination dwbits in
    let rec gather_attribs attriblist dwbits =
      let attr_code, dwbits = parse_uleb128_int dwbits in
      let attr_form_code, dwbits = parse_uleb128_int dwbits in
      if attr_code = 0 && attr_form_code = 0 then
	attriblist, dwbits
      else begin
	let attr = parse_attribute attr_code
	and attr_form = parse_attribute_form attr_form_code in
	gather_attribs ((attr, attr_form) :: attriblist) dwbits
      end in
    let attribs, dwbits = gather_attribs [] dwbits in
    Some (num, tag, List.rev attribs, has_children), dwbits
  end

(* Parse the abbreviations for a single compilation unit.  *)

let parse_abbrevs dwbits =
  let rec build abbrevs dwbits =
    let abbrev, dwbits = parse_one_abbrev dwbits in
    match abbrev with
      None -> Array.of_list (List.rev abbrevs)
    | Some (num, tag, attribs, has_children) ->
        build ({ abv_num = num; abv_tag = tag; abv_attribs = attribs;
		 abv_has_children = has_children } :: abbrevs) dwbits in
  build [] dwbits

(* Parse multiple abbreviation tables from multiple compilation units (in a
   single section).  (This is useless! Once we parse compilation unit header
   in .debug_info, we get an offset to the proper data.)  *)

(*let parse_all_abbrevs dwbits =
  let rec build culist dwbits =
    if Bitstring.bitstring_length dwbits = 0 then
      culist
    else begin
      let abbrevs, dwbits = parse_abbrevs dwbits in
      build (abbrevs :: culist) dwbits
    end in
  List.rev (build [] dwbits)*)

let sign_extend x bit =
  let signbit = 1 lsl bit in
  if x < (signbit lsr 1) then x else x - signbit

let parse_operation dwbits ~addr_size =
  let next_byte = Bitstring.dropbits 8 dwbits in
  bitmatch dwbits with
    { 0x03 : 8 : littleendian;
      addr : addr_size : littleendian;
      rest : -1 : bitstring } -> `DW_OP_addr addr, rest
  | { 0x06 : 8 : littleendian } -> `DW_OP_deref, next_byte
  | { 0x08 : 8 : littleendian;
      cst : 8 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const1u cst, rest
  | { 0x09 : 8 : littleendian;
      cst : 8 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const1s (sign_extend cst 8), rest
  | { 0x0a : 8 : littleendian;
      cst : 16 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const2u cst, rest
  | { 0x0b : 8 : littleendian;
      cst : 16 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const2s (sign_extend cst 16), rest
  | { 0x0c : 8 : littleendian;
      cst : 32 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const4u cst, rest
  | { 0x0d : 8 : littleendian;
      cst : 32 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const4s cst, rest
  | { 0x0e : 8 : littleendian;
      cst : 64 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const8u cst, rest
  | { 0x0f : 8 : littleendian;
      cst : 64 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_const8s cst, rest
  | { 0x10 : 8 : littleendian;
      cst_rest : -1 : bitstring } ->
        let uleb, rest = parse_uleb128 cst_rest in
	`DW_OP_constu uleb, rest
  | { 0x11 : 8 : littleendian;
      cst_rest : -1 : bitstring } ->
        let sleb, rest = parse_sleb128 cst_rest in
	`DW_OP_consts sleb, rest
  | { 0x12 : 8 : littleendian } -> `DW_OP_dup, next_byte
  | { 0x13 : 8 : littleendian } -> `DW_OP_drop, next_byte
  | { 0x14 : 8 : littleendian } -> `DW_OP_over, next_byte
  | { 0x15 : 8 : littleendian;
      idx : 8 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_pick idx, rest
  | { 0x16 : 8 : littleendian } -> `DW_OP_swap, next_byte
  | { 0x17 : 8 : littleendian } -> `DW_OP_rot, next_byte
  | { 0x18 : 8 : littleendian } -> `DW_OP_xderef, next_byte
  | { 0x19 : 8 : littleendian } -> `DW_OP_abs, next_byte
  | { 0x1a : 8 : littleendian } -> `DW_OP_and, next_byte
  | { 0x1b : 8 : littleendian } -> `DW_OP_div, next_byte
  | { 0x1c : 8 : littleendian } -> `DW_OP_minus, next_byte
  | { 0x1d : 8 : littleendian } -> `DW_OP_mod, next_byte
  | { 0x1e : 8 : littleendian } -> `DW_OP_mul, next_byte
  | { 0x1f : 8 : littleendian } -> `DW_OP_neg, next_byte
  | { 0x20 : 8 : littleendian } -> `DW_OP_not, next_byte
  | { 0x21 : 8 : littleendian } -> `DW_OP_or, next_byte
  | { 0x22 : 8 : littleendian } -> `DW_OP_plus, next_byte
  | { 0x23 : 8 : littleendian;
      cst_rest : -1 : bitstring } ->
        let cst, rest = parse_uleb128 cst_rest in
	`DW_OP_plus_uconst cst, rest
  | { 0x24 : 8 : littleendian } -> `DW_OP_shl, next_byte
  | { 0x25 : 8 : littleendian } -> `DW_OP_shr, next_byte
  | { 0x26 : 8 : littleendian } -> `DW_OP_shra, next_byte
  | { 0x27 : 8 : littleendian } -> `DW_OP_xor, next_byte
  | { 0x2f : 8 : littleendian;
      cst : 16 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_skip (sign_extend cst 16), rest
  | { 0x28 : 8 : littleendian;
      cst : 16 : littleendian;
      rest : -1 : bitstring } -> `DW_OP_bra (sign_extend cst 16), rest
  | { 0x29 : 8 : littleendian } -> `DW_OP_eq, next_byte
  | { 0x2a : 8 : littleendian } -> `DW_OP_ge, next_byte
  | { 0x2b : 8 : littleendian } -> `DW_OP_gt, next_byte
  | { 0x2c : 8 : littleendian } -> `DW_OP_le, next_byte
  | { 0x2d : 8 : littleendian } -> `DW_OP_lt, next_byte
  | { 0x2e : 8 : littleendian } -> `DW_OP_ne, next_byte
  | { lit : 8 : littleendian } when lit >= 0x30 && lit <= 0x4f ->
      `DW_OP_lit (lit - 0x30), next_byte
  | { regno : 8 : littleendian } when regno >= 0x50 && regno <= 0x6f ->
      `DW_OP_reg (regno - 0x50), next_byte
  | { bregno : 8 : littleendian;
      cst_rest : -1 : bitstring } when bregno >= 0x70 && bregno <= 0x8f ->
        let cst, rest = parse_sleb128 cst_rest in
	`DW_OP_breg (bregno - 0x70, cst), rest
  | { 0x90 : 8 : littleendian;
      regno_rest : -1 : bitstring } ->
        let regno, rest = parse_uleb128 regno_rest in
        `DW_OP_regx (Big_int.int_of_big_int regno), rest
  | { 0x91 : 8 : littleendian;
      offset_rest : -1 : bitstring } ->
        let offset, rest = parse_sleb128 offset_rest in
	`DW_OP_fbreg (Big_int.int_of_big_int offset), rest
  | { 0x92 : 8 : littleendian;
      bregx_rest : -1 : bitstring } ->
        let reg, offset_rest = parse_uleb128 bregx_rest in
	let offset, rest = parse_sleb128 offset_rest in
	`DW_OP_bregx (reg, offset), rest
  | { 0x93 : 8 : littleendian;
      piece_rest : -1 : bitstring } ->
        let piece, rest = parse_uleb128 piece_rest in
        `DW_OP_piece (Big_int.int_of_big_int piece), rest
  | { 0x94 : 8 : littleendian;
      datasize : 8 : littleendian;
      rest : -1 : bitstring } ->
        `DW_OP_deref_size datasize, rest
  | { 0x95 : 8 : littleendian;
      datasize : 8 : littleendian;
      rest : -1 : bitstring } ->
        `DW_OP_xderef_size datasize, rest
  | { 0x96 : 8 : littleendian } -> `DW_OP_nop, next_byte
  | { 0x97 : 8 : littleendian } -> `DW_OP_push_object_address, next_byte
  | { 0x98 : 8 : littleendian;
      offset : 16 : littleendian;
      rest : -1 : bitstring } ->
        `DW_OP_call2 (sign_extend offset 16), rest
  | { 0x99 : 8 : littleendian;
      offset : 32 : littleendian;
      rest : -1 : bitstring } ->
        `DW_OP_call4 offset, rest
  | { 0x9a : 8 : littleendian;
      offset : 32 : littleendian;	(* 32-bit Dwarf.  *)
      rest : -1 : bitstring } ->
        `DW_OP_call_ref offset, rest
  | { 0x9b : 8 : littleendian } -> `DW_OP_form_tls_address, next_byte
  | { 0x9c : 8 : littleendian } -> `DW_OP_call_frame_cfa, next_byte
  | { 0x9d : 8 : littleendian;
      st_en_rest : -1 : bitstring } ->
        let st, en_rest = parse_uleb128 st_en_rest in
	let en, rest = parse_uleb128 en_rest in
        `DW_OP_bit_piece (st, en), rest
  | { 0xe0 : 8 : littleendian } -> `DW_OP_lo_user, next_byte
  | { 0xff : 8 : littleendian } -> `DW_OP_hi_user, next_byte

type comp_unit_header =
  {
    unit_length : int32;
    version : int;
    debug_abbrev_offset : int32;
    address_size : int
  }

let parse_comp_unit_header dwbits =
  bitmatch dwbits with
    { unit_length : 32 : littleendian;
      version : 16 : littleendian;
      debug_abbrev_offset : 32 : littleendian;
      address_size : 8 : littleendian;
      rest : -1 : bitstring } ->
      { unit_length = unit_length;
        version = version;
	debug_abbrev_offset = debug_abbrev_offset;
	address_size = address_size }, rest
  | { _ } -> raise (Dwarf_parse_error "parse_comp_unit_header")

let rec parse_form dwbits form ~addr_size ~string_sec =
  match form with
    DW_FORM_addr ->
      (bitmatch dwbits with
        { addr : 32 : littleendian;
	  rest : -1 : bitstring } -> `addr addr, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form addr"))
  | DW_FORM_block1 ->
      (bitmatch dwbits with
        { length : 8 : littleendian;
	  rest : -1 : bitstring } ->
	  let bitlength = length * 8 in
	  `block (Bitstring.takebits bitlength rest),
	    Bitstring.dropbits bitlength rest
      | { _ } -> raise (Dwarf_parse_error "parse_form block1"))
  | DW_FORM_block2 ->
      (bitmatch dwbits with
        { length : 16 : littleendian;
	  rest : -1 : bitstring } ->
	  let bitlength = length * 8 in
	  `block (Bitstring.takebits bitlength rest),
	    Bitstring.dropbits bitlength rest
      | { _ } -> raise (Dwarf_parse_error "parse_form block2"))
  | DW_FORM_block4 ->
      (bitmatch dwbits with
        { length : 32 : littleendian;
	  rest : -1 : bitstring } ->
	  let bitlength = (Int32.to_int length) * 8 in
	  `block (Bitstring.takebits bitlength rest),
	    Bitstring.dropbits bitlength rest
      | { _ } -> raise (Dwarf_parse_error "parse_form block4"))
  | DW_FORM_block ->
      let length, rest = parse_uleb128_int dwbits in
      let bitlength = length * 8 in
      `block (Bitstring.takebits bitlength rest),
	Bitstring.dropbits bitlength rest
  | DW_FORM_data1 ->
      (bitmatch dwbits with
        { data : 8 : littleendian;
	  rest : -1 : bitstring } -> `data1 data, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form data1"))
  | DW_FORM_data2 ->
      (bitmatch dwbits with
        { data : 16 : littleendian;
	  rest : -1 : bitstring } -> `data2 data, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form data1"))
  | DW_FORM_data4 ->
      (bitmatch dwbits with
        { data : 32 : littleendian;
	  rest : -1 : bitstring } -> `data4 data, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form data1"))
  | DW_FORM_data8 ->
      (bitmatch dwbits with
        { data : 64 : littleendian;
	  rest : -1 : bitstring } -> `data8 data, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form data1"))
  | DW_FORM_sdata ->
      let data, rest = parse_sleb128 dwbits in
      `sdata data, rest
  | DW_FORM_udata ->
      let data, rest = parse_uleb128 dwbits in
      `udata data, rest
  | DW_FORM_string ->
      let b = Buffer.create 10 in
      let rec gather bits =
        bitmatch bits with
          { "\000" : 8 : string; rest : -1 : bitstring } ->
	    Buffer.contents b, rest
	| { c : 8 : string; rest : -1 : bitstring } ->
	    Buffer.add_string b c;
	    gather rest in
      let str, rest = gather dwbits in
      `string str, rest
  | DW_FORM_strp ->
      (bitmatch dwbits with
        { offset : 32 : littleendian;
	  rest : -1 : bitstring } ->
	  `string (Elfreader.get_string string_sec (Int32.to_int offset)), rest
      | { _ } -> raise (Dwarf_parse_error "parse_form strp"))
  | DW_FORM_flag ->
      (bitmatch dwbits with
        { flag : 8 : littleendian;
	  rest : -1 : bitstring } ->
	  `flag (flag != 0), rest
      | { _ } -> raise (Dwarf_parse_error "parse_form flag"))
  | DW_FORM_ref_addr ->
      raise (Dwarf_parse_error "parse_form ref_addr")
  | DW_FORM_ref1 ->
      (bitmatch dwbits with
        { reference : 8 : littleendian;
	  rest : -1 : bitstring } ->
	  `ref1 reference, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form ref1"))
  | DW_FORM_ref2 ->
      (bitmatch dwbits with
        { reference : 16 : littleendian;
	  rest : -1 : bitstring } ->
	  `ref2 reference, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form ref2"))
  | DW_FORM_ref4 ->
      (bitmatch dwbits with
        { reference : 32 : littleendian;
	  rest : -1 : bitstring } ->
	  `ref4 reference, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form ref4"))
  | DW_FORM_ref8 ->
      (bitmatch dwbits with
        { reference : 64 : littleendian;
	  rest : -1 : bitstring } ->
	  `ref8 reference, rest
      | { _ } -> raise (Dwarf_parse_error "parse_form ref8"))
  | DW_FORM_ref_udata ->
      let data, rest = parse_uleb128 dwbits in
      `uref data, rest
  | DW_FORM_indirect ->
      let form_code, rest = parse_uleb128_int dwbits in
      let form = parse_attribute_form form_code in
      parse_form rest form ~addr_size ~string_sec

type 'a die =
    Die_node of 'a * 'a die
  | Die_tree of 'a * 'a die * 'a die
  | Die_empty

let parse_one_die dwbits ~abbrevs ~addr_size ~string_sec =
  let abbrev_code, dwbits = parse_uleb128_int dwbits in
  if abbrev_code = 0 then
    None, dwbits
  else begin
    let abbrev = abbrevs.(abbrev_code - 1) in
    if abbrev.abv_num != abbrev_code then
      failwith "Hmm, I expected contiguous numbering in .dwarf_abbrev";
    let attr_vals, dwbits = List.fold_left
      (fun (parsed, dwbits) (attr, form) ->
	let data, dwbits = parse_form dwbits form ~addr_size ~string_sec in
	(attr, data) :: parsed, dwbits)
      ([], dwbits)
      abbrev.abv_attribs in
    Some (abbrev.abv_tag, attr_vals, abbrev.abv_has_children), dwbits
  end

(* Parse a tree of DIE information.  Siblings are represented as a Die_node,
   children as a Die_tree.
   LENGTH should be the full length of the DIE section, including CU header.  *)

let parse_die dwbits ~length ~abbrevs ~addr_size ~string_sec =
  let die_hash = Hashtbl.create 10 in
  let rec build dwbits depth =
    let offset_bits = length - (Bitstring.bitstring_length dwbits) in
    let offset = offset_bits / 8 in
    (* Printf.printf "parsing die, offset %d\n" offset; *)
    let things, dwbits = parse_one_die dwbits ~abbrevs ~addr_size ~string_sec in
    match things with
      Some (tag, attr_vals, has_children) ->
        let data = tag, attr_vals in
	let cdepth = if has_children then succ depth else depth in
	let child_or_sibling, dwbits' = build dwbits cdepth in
        let this_node, dwbits' =
	  if has_children then begin
	    (* This is kind of ugly: the top-level die must be
	       DW_TAG_compile_unit, and does *not* form a sibling list, so is
	       not terminated with a null entry.  This is kind of a special
	       case, but saves a single byte per CU in the binary.  Woohoo!  *)
	    if depth = 0 then
	      Die_node (data, child_or_sibling), dwbits'
	    else begin
	      let sibling, dwbits'' = build dwbits' depth in
	      Die_tree (data, child_or_sibling, sibling), dwbits''
	    end
	  end else
	    Die_node (data, child_or_sibling), dwbits' in
	Hashtbl.add die_hash offset this_node;
	this_node, dwbits'
    | None -> Die_empty, dwbits in
  let dies, dwbits' = build dwbits 0 in
  dies, die_hash, dwbits'

exception Type_mismatch of string

let get_attr_string attrs typ =
  match List.assoc typ attrs with
    `string foo -> foo
  | _ -> raise (Type_mismatch "string")

let get_attr_string_opt attrs typ =
  try get_attr_string attrs typ
  with Not_found -> "(none)"

let get_attr_int32 attrs typ =
  match List.assoc typ attrs with
    `data1 v | `data2 v -> Int32.of_int v
  | `data4 v -> v
  | `sdata v -> Big_int.int32_of_big_int v
  | _ -> raise (Type_mismatch "int32")

let get_attr_int attrs typ =
  Int32.to_int (get_attr_int32 attrs typ)

let get_attr_address attrs typ =
  match List.assoc typ attrs with
    `addr a -> a
  | _ -> raise (Type_mismatch "address")

let get_attr_ref attrs typ =
  match List.assoc typ attrs with
    `ref1 r | `ref2 r -> Int32.of_int r
  | `ref4 r -> r
  | _ -> raise (Type_mismatch "ref")

let lookup_die tref hash =
  Hashtbl.find hash (Int32.to_int tref)

let get_attr_deref attrs typ hash =
  let die_ref = get_attr_ref attrs typ in
  lookup_die die_ref hash

let attr_present attrs typ =
  List.mem_assoc typ attrs
