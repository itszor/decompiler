exception Dwarf_parse_error of string

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
	  Big_int.add_int_big_int chunk
	    (Big_int.shift_left_big_int higher_bits 7), rest'
    | { _ } -> raise (Dwarf_parse_error "uleb128") in
  build dwbits

let signed_value x =
  if x < 64 then x else x - 128

(* Parse SLEB128 value in DWBITS to a Big_int.  *)

let parse_sleb128 dwbits =
  let rec build bits =
    bitmatch bits with
      { chunk : 7 : littleendian;
        false : 1 : littleendian;
	rest : -1 : bitstring } ->
	  Big_int.big_int_of_int (signed_value chunk), rest
    | { chunk : 7 : littleendian;
        true : 1 : littleendian;
	rest : -1 : bitstring } ->
	  let higher_bits, rest' = build rest in
	  Big_int.add_int_big_int (signed_value chunk)
	    (Big_int.shift_left_big_int higher_bits 7), rest'
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

let parse_tag = function
    0x01 -> `DW_TAG_array_type
  | 0x02 -> `DW_TAG_class_type
  | 0x03 -> `DW_TAG_entry_point
  | 0x04 -> `DW_TAG_enumeration_type
  | 0x05 -> `DW_TAG_formal_parameter
  | 0x08 -> `DW_TAG_imported_declaration
  | 0x0a -> `DW_TAG_label
  | 0x0b -> `DW_TAG_lexical_block
  | 0x0d -> `DW_TAG_member
  | 0x0f -> `DW_TAG_pointer_type
  | 0x10 -> `DW_TAG_reference_type
  | 0x11 -> `DW_TAG_compile_unit
  | 0x12 -> `DW_TAG_string_type
  | 0x13 -> `DW_TAG_structure_type
  | 0x15 -> `DW_TAG_subroutine_type
  | 0x16 -> `DW_TAG_typedef
  | 0x17 -> `DW_TAG_union_type
  | 0x18 -> `DW_TAG_unspecified_parameters
  | 0x19 -> `DW_TAG_variant
  | 0x1a -> `DW_TAG_common_block
  | 0x1b -> `DW_TAG_common_inclusion
  | 0x1c -> `DW_TAG_inheritance
  | 0x1d -> `DW_TAG_inlined_subroutine
  | 0x1e -> `DW_TAG_module
  | 0x1f -> `DW_TAG_ptr_to_member_type
  | 0x20 -> `DW_TAG_set_type
  | 0x21 -> `DW_TAG_subrange_type
  | 0x22 -> `DW_TAG_with_stmt
  | 0x23 -> `DW_TAG_access_declaration
  | 0x24 -> `DW_TAG_base_type
  | 0x25 -> `DW_TAG_catch_block
  | 0x26 -> `DW_TAG_const_type
  | 0x27 -> `DW_TAG_constant
  | 0x28 -> `DW_TAG_enumerator
  | 0x29 -> `DW_TAG_file_type
  | 0x2a -> `DW_TAG_friend
  | 0x2b -> `DW_TAG_namelist
  | 0x2c -> `DW_TAG_namelist_item
  | 0x2d -> `DW_TAG_packed_type
  | 0x2e -> `DW_TAG_subprogram
  | 0x2f -> `DW_TAG_template_type_parameter
  | 0x30 -> `DW_TAG_template_value_parameter
  | 0x31 -> `DW_TAG_thrown_type
  | 0x32 -> `DW_TAG_try_block
  | 0x33 -> `DW_TAG_variant_part
  | 0x34 -> `DW_TAG_variable
  | 0x35 -> `DW_TAG_volatile_type
  | 0x36 -> `DW_TAG_dwarf_procedure
  | 0x37 -> `DW_TAG_restrict_type
  | 0x38 -> `DW_TAG_interface_type
  | 0x39 -> `DW_TAG_namespace
  | 0x3a -> `DW_TAG_imported_module
  | 0x3b -> `DW_TAG_unspecified_type
  | 0x3c -> `DW_TAG_partial_unit
  | 0x3d -> `DW_TAG_imported_unit
  | 0x3f -> `DW_TAG_condition
  | 0x40 -> `DW_TAG_shared_type
  | 0x4080 -> `DW_TAG_lo_user
  | 0xffff -> `DW_TAG_hi_user
  | _ -> raise (Dwarf_parse_error "parse_tag")

let parse_child_determination dwbits =
  bitmatch dwbits with
    { 0x00 : 8 : littleendian; rest : -1 : bitstring } -> false, rest
  | { 0x01 : 8 : littleendian; rest : -1 : bitstring } -> true, rest
  | { _ } -> raise (Dwarf_parse_error "parse_child_determination")

let parse_attribute = function
    0x01 -> `DW_AT_sibling
  | 0x02 -> `DW_AT_location
  | 0x03 -> `DW_AT_name
  | 0x09 -> `DW_AT_ordering
  | 0x0b -> `DW_AT_byte_size
  | 0x0c -> `DW_AT_bit_offset
  | 0x0d -> `DW_AT_bit_size
  | 0x10 -> `DW_AT_stmt_list
  | 0x11 -> `DW_AT_low_pc
  | 0x12 -> `DW_AT_high_pc
  | 0x13 -> `DW_AT_language
  | 0x15 -> `DW_AT_discr
  | 0x16 -> `DW_AT_discr_value
  | 0x17 -> `DW_AT_visibility
  | 0x18 -> `DW_AT_import
  | 0x19 -> `DW_AT_string_length
  | 0x1a -> `DW_AT_common_reference
  | 0x1b -> `DW_AT_comp_dir
  | 0x1c -> `DW_AT_const_value
  | 0x1d -> `DW_AT_containing_type
  | 0x1e -> `DW_AT_default_value
  | 0x20 -> `DW_AT_inline
  | 0x21 -> `DW_AT_is_optional
  | 0x22 -> `DW_AT_lower_bound
  | 0x25 -> `DW_AT_producer
  | 0x27 -> `DW_AT_prototyped
  | 0x2a -> `DW_AT_return_addr
  | 0x2c -> `DW_AT_start_scope
  | 0x2e -> `DW_AT_bit_stride
  | 0x2f -> `DW_AT_upper_bound
  | 0x31 -> `DW_AT_abstract_origin
  | 0x32 -> `DW_AT_accessibility
  | 0x33 -> `DW_AT_address_class
  | 0x34 -> `DW_AT_artificial
  | 0x35 -> `DW_AT_base_types
  | 0x36 -> `DW_AT_calling_convention
  | 0x37 -> `DW_AT_count
  | 0x38 -> `DW_AT_data_member_location
  | 0x39 -> `DW_AT_decl_column
  | 0x3a -> `DW_AT_decl_file
  | 0x3b -> `DW_AT_decl_line
  | 0x3c -> `DW_AT_declaration
  | 0x3d -> `DW_AT_discr_list
  | 0x3e -> `DW_AT_encoding
  | 0x3f -> `DW_AT_external
  | 0x40 -> `DW_AT_frame_base
  | 0x41 -> `DW_AT_friend
  | 0x42 -> `DW_AT_identifier_case
  | 0x43 -> `DW_AT_macro_info
  | 0x44 -> `DW_AT_namelist_item
  | 0x45 -> `DW_AT_priority
  | 0x46 -> `DW_AT_segment
  | 0x47 -> `DW_AT_specification
  | 0x48 -> `DW_AT_static_link
  | 0x49 -> `DW_AT_type
  | 0x4a -> `DW_AT_use_location
  | 0x4b -> `DW_AT_variable_parameter
  | 0x4c -> `DW_AT_virtuality
  | 0x4d -> `DW_AT_vtable_elem_location
  | 0x4e -> `DW_AT_allocated
  | 0x4f -> `DW_AT_associated
  | 0x50 -> `DW_AT_data_location
  | 0x51 -> `DW_AT_byte_stride
  | 0x52 -> `DW_AT_entry_pc
  | 0x53 -> `DW_AT_use_UTF8
  | 0x54 -> `DW_AT_extension
  | 0x55 -> `DW_AT_ranges
  | 0x56 -> `DW_AT_trampoline
  | 0x57 -> `DW_AT_call_column
  | 0x58 -> `DW_AT_call_file
  | 0x59 -> `DW_AT_call_line
  | 0x5a -> `DW_AT_description
  | 0x5b -> `DW_AT_binary_scale
  | 0x5c -> `DW_AT_decimal_scale
  | 0x5d -> `DW_AT_small
  | 0x5e -> `DW_AT_decimal_sign
  | 0x5f -> `DW_AT_digit_count
  | 0x60 -> `DW_AT_picture_string
  | 0x61 -> `DW_AT_mutable
  | 0x62 -> `DW_AT_threads_scaled
  | 0x63 -> `DW_AT_explicit
  | 0x64 -> `DW_AT_object_pointer
  | 0x65 -> `DW_AT_endianity
  | 0x66 -> `DW_AT_elemental
  | 0x67 -> `DW_AT_pure
  | 0x68 -> `DW_AT_recursive
  | 0x2000 -> `DW_AT_lo_user
  | 0x3fff -> `DW_AT_hi_user
  | _ -> raise (Dwarf_parse_error "parse_attribute")

let parse_attribute_form = function
    0x01 -> `DW_FORM_addr
  | 0x03 -> `DW_FORM_block2
  | 0x04 -> `DW_FORM_block4
  | 0x05 -> `DW_FORM_data2
  | 0x06 -> `DW_FORM_data4
  | 0x07 -> `DW_FORM_data8
  | 0x08 -> `DW_FORM_string
  | 0x09 -> `DW_FORM_block
  | 0x0a -> `DW_FORM_block1
  | 0x0b -> `DW_FORM_data1
  | 0x0c -> `DW_FORM_flag
  | 0x0d -> `DW_FORM_sdata
  | 0x0e -> `DW_FORM_strp
  | 0x0f -> `DW_FORM_udata
  | 0x10 -> `DW_FORM_ref_addr
  | 0x11 -> `DW_FORM_ref1
  | 0x12 -> `DW_FORM_ref2
  | 0x13 -> `DW_FORM_ref4
  | 0x14 -> `DW_FORM_ref8
  | 0x15 -> `DW_FORM_ref_udata
  | 0x16 -> `DW_FORM_indirect
  | _ -> raise (Dwarf_parse_error "parse_attribute_form")

type ('a, 'b) dwarf_abbrev =
  {
    abv_num : int;
    abv_tag : 'a;
    abv_attribs : 'b list;
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
      None -> List.rev abbrevs, dwbits
    | Some (num, tag, attribs, has_children) ->
        build ({ abv_num = num; abv_tag = tag; abv_attribs = attribs;
		 abv_has_children = has_children } :: abbrevs) dwbits in
  build [] dwbits

(* Parse multiple abbreviation tables from multiple compilation units (in a
   single section).  (This is useless! Once we parse compilation unit header
   in .debug_info, we get an offset to the proper data.)  *)

let parse_all_abbrevs dwbits =
  let rec build culist dwbits =
    if Bitstring.bitstring_length dwbits = 0 then
      culist
    else begin
      let abbrevs, dwbits = parse_abbrevs dwbits in
      build (abbrevs :: culist) dwbits
    end in
  List.rev (build [] dwbits)

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

open Elfreader

let elfbits, ehdr = read_file "libGLESv2.so"
let shdr_arr = get_section_headers elfbits ehdr
let debug_abbrev = get_section_by_name elfbits ehdr shdr_arr ".debug_abbrev"
let abbrevs = parse_all_abbrevs debug_abbrev
