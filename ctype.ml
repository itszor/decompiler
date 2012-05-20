open Dwarfreader

(* This is (so far) a really bad approximation of the C type system!  *)

type ctype =
    C_void
  | C_int
  | C_short
  | C_char
  | C_float
  | C_double
  | C_signed of ctype
  | C_unsigned of ctype
  | C_pointer of (unit -> ctype)
  | C_const of ctype
  | C_volatile of ctype
  | C_struct of aggregate_member list
  | C_union of aggregate_member list
  | C_array of int * ctype
  | C_enum (* of ... *)

and aggregate_member = {
  name : string;
  typ : ctype
}

exception Unknown_type

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
  | Die_node ((DW_TAG_const_type, attrs), _) ->
      let targ = get_attr_deref attrs DW_AT_type die_hash in
      C_const (build targ)
  | Die_node ((DW_TAG_volatile_type, attrs), _) ->
      let targ = get_attr_deref attrs DW_AT_type die_hash in
      C_volatile (build targ)
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

