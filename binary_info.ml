open Elfreader
open Dwarfreader

type cu_info = {
  (* Debug info entries for compilation unit, indexed by offset into table.  *)
  ci_dietab : (int, tag_attr_die) Hashtbl.t;
  (* Symbols defined in CU, indexed by symbol address.  *)
  ci_symtab : (int32, elf_sym) Hashtbl.t;
  (* Debug info entries for symbol address, indexed by "low PC".  *)
  ci_dieaddr : (int32, tag_attr_die) Hashtbl.t
}

type binary_info = {
  elfbits : Bitstring.bitstring;
  ehdr : elf_ehdr;
  shdr_arr : elf_shdr array;
  debug_info : Bitstring.bitstring;
  debug_abbrev : Bitstring.bitstring;
  debug_str_sec : Bitstring.bitstring;
  debug_line : Bitstring.bitstring;
  debug_pubnames : Bitstring.bitstring;
  debug_aranges : Bitstring.bitstring;
  lines : Line.line_prog_hdr;
  text : Bitstring.bitstring;
  strtab : Bitstring.bitstring;
  symtab : Bitstring.bitstring;
  symbols : elf_sym list;
  mapping_syms : elf_sym list;
  (* Parsed arange data.  *)
  parsed_aranges : (aranges_header * (int32 * int32) list) list;
  (* Hashtbl of cu_infos, indexed by debug_info offset.  *)
  cu_hash : (int32, cu_info) Hashtbl.t
}

let index_dies_by_low_pc dieaddr_ht dies =
  let rec scan = function
    Die_node ((DW_TAG_compile_unit, _), children) ->
      scan children
  | Die_tree ((DW_TAG_subprogram, sp_attrs), children, sibl) as die ->
      begin try
        (*let name = get_attr_string sp_attrs DW_AT_name in*)
        let lowpc = get_attr_address sp_attrs DW_AT_low_pc in
	(*Printf.printf "name: '%s', low pc: %lx\n" name lowpc;*)
	Hashtbl.add dieaddr_ht lowpc die
      with Not_found -> ()
      end;
      scan children;
      scan sibl
  | Die_tree (_, children, sibl) ->
      scan children;
      scan sibl
  | Die_node (_, sibl) ->
      scan sibl
  | Die_empty -> ()
  in
  scan dies

let index_debug_data binf parsed_data =
  List.iter
    (fun (ar_hdr, ranges) ->
      let debug_inf_for_hdr =
        offset_section binf.debug_info ar_hdr.ar_debug_info_offset in
	let cu_header, after_cu_hdr =
	  parse_comp_unit_header debug_inf_for_hdr in
	  let debug_abbr_offset = cu_header.debug_abbrev_offset in
	  let debug_abbr = offset_section binf.debug_abbrev debug_abbr_offset in
	  let abbrevs = parse_abbrevs debug_abbr in
	  let cu_dies, die_hash, _ =
	    parse_die_for_cu after_cu_hdr
	      ~length:(Bitstring.bitstring_length debug_inf_for_hdr)
	      ~abbrevs:abbrevs ~addr_size:cu_header.address_size
	      ~string_sec:binf.debug_str_sec in
	  let cu_inf = {
	    ci_dietab = die_hash;
	    ci_symtab = Hashtbl.create 10;
	    ci_dieaddr = Hashtbl.create 10
	  } in
	  List.iter
	    (fun (start, len) ->
	      let syms =
	        Symbols.find_symbols_for_addr_range binf.symbols start
						    (Int32.add start len) in
	      List.iter
	        (fun sym ->
		  match Symbols.symbol_type sym with
		    Symbols.STT_FUNC ->
		      Hashtbl.add cu_inf.ci_symtab sym.st_value sym
		  | _ -> ())
		syms)
	    ranges;
	  index_dies_by_low_pc cu_inf.ci_dieaddr cu_dies;
	  Hashtbl.add binf.cu_hash ar_hdr.ar_debug_info_offset cu_inf)
    parsed_data

let open_file filename =
  let elfbits, ehdr = read_file filename in
  let shdr_arr = get_section_headers elfbits ehdr in
  let debug_info = get_section_by_name elfbits ehdr shdr_arr ".debug_info" in
  let debug_abbrev = get_section_by_name elfbits ehdr shdr_arr
					 ".debug_abbrev" in
  let debug_str_sec = get_section_by_name elfbits ehdr shdr_arr ".debug_str" in
  let debug_line = get_section_by_name elfbits ehdr shdr_arr ".debug_line" in
  let debug_pubnames = get_section_by_name elfbits ehdr shdr_arr
					   ".debug_pubnames" in
  let debug_aranges = get_section_by_name elfbits ehdr shdr_arr
					  ".debug_aranges" in
  let lines, _ = Line.parse_lines debug_line in
  let text = get_section_by_name elfbits ehdr shdr_arr ".text" in
  let strtab = get_section_by_name elfbits ehdr shdr_arr ".strtab" in
  let symtab = get_section_by_name elfbits ehdr shdr_arr ".symtab" in
  let symbols = Symbols.read_symbols symtab in
  let mapping_syms = Mapping.get_mapping_symbols elfbits ehdr shdr_arr strtab
		     symbols ".text" in
  let ar = parse_all_arange_data debug_aranges in
  let binf = {
    elfbits = elfbits;
    ehdr = ehdr;
    shdr_arr = shdr_arr;
    debug_info = debug_info;
    debug_abbrev = debug_abbrev;
    debug_str_sec = debug_str_sec;
    debug_line = debug_line;
    debug_pubnames = debug_pubnames;
    debug_aranges = debug_aranges;
    lines = lines;
    text = text;
    strtab = strtab;
    symtab = symtab;
    symbols = symbols;
    mapping_syms = mapping_syms;
    parsed_aranges = ar;
    cu_hash = Hashtbl.create 10
  } in
  index_debug_data binf ar;
  binf

(* Given an address, find the compilation unit offset into the debug_info
   section.  This can be used to lookup CU_HASH in BINF.  *)

let cu_offset_for_address binf addr =
  let ar_hdr, _ = List.find
    (fun (ar_hdr, ranges) ->
      List.exists (fun (lo, len) -> addr >= lo && addr < (Int32.add lo len))
		  ranges)
    binf.parsed_aranges in
  ar_hdr.ar_debug_info_offset
