open Elfreader
open Dwarfreader
open Dwarfprint

let elfbits, ehdr = read_file "libGLESv2.so"
let shdr_arr = get_section_headers elfbits ehdr
let debug_info = get_section_by_name elfbits ehdr shdr_arr ".debug_info"
let debug_info_len = Bitstring.bitstring_length debug_info
let cu_header, remaining_debug_info = parse_comp_unit_header debug_info
let debug_abbrev = get_section_by_name elfbits ehdr shdr_arr ".debug_abbrev"
let debug_str_sec = get_section_by_name elfbits ehdr shdr_arr ".debug_str"
let cu_debug_abbrev = offset_section debug_abbrev cu_header.debug_abbrev_offset
let abbrevs = parse_abbrevs cu_debug_abbrev
let debug_line = get_section_by_name elfbits ehdr shdr_arr ".debug_line"
let lines, remaining_debug_line = Line.parse_lines debug_line
let text = get_section_by_name elfbits ehdr shdr_arr ".text"
let code, remaining_code = Decode_arm.decode_insns text 10

let debug_info_ptr = ref remaining_debug_info
let fetch_die () =
  let die_tree, die_hash, next_die = parse_die !debug_info_ptr
				     ~length:debug_info_len
				     ~abbrevs ~addr_size:cu_header.address_size
				     ~string_sec:debug_str_sec in
  debug_info_ptr := next_die;
  die_tree, die_hash

(*let _ =
  let x, h = fetch_die () in
  print_all_dies x h*)

(* Next, we need to decode .debug_line!  *)
