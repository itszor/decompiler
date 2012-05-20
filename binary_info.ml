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
  (* Hashtbl of cu_infos, indexed by debug_info offset.  *)
  cu_hash : (int32, cu_info) Hashtbl.t
}

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
  {
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
    cu_hash = Hashtbl.create 10
  }
