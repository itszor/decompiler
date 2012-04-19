open Elfreader
open Dwarfreader
open Dwarfprint

let elfbits, ehdr = read_file "foo"
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
(*let code, remaining_code = Decode_arm.decode_insns text 40*)
let strtab = get_section_by_name elfbits ehdr shdr_arr ".strtab"
let symtab = get_section_by_name elfbits ehdr shdr_arr ".symtab"
let symbols = Symbols.read_symbols symtab

(*
let code_for_sym symname =
  let sym = Symbols.find_named_symbol symbols strtab symname in
  let start_offset = Int32.sub sym.st_value
			       shdr_arr.(sym.st_shndx).sh_addr in
  let insns, _ = Decode_arm.decode_insns
		   (Bitstring.dropbits (8 * (Int32.to_int start_offset)) text)
		   ((Int32.to_int sym.st_size) / 4) in
  insns
*)

let strip_condition = function
    Insn.Conditional (_, opcode) -> opcode
  | opcode -> opcode

exception Not_PC_relative

let absolute_address addr operand =
  match operand with
    Insn.PC_relative offset -> Int32.add addr offset
  | _ -> raise Not_PC_relative

module LabelSet = Set.Make
  (struct
    type t = int32
    let compare = compare
  end)

(* Return a list of addresses which (could be) labels/block start addresses
   for INSN.  *)

let targets addr insn labelset =
  match strip_condition insn.Insn.opcode with
    Insn.B
  | Insn.Bl
  | Insn.Bx ->
      begin try
	let labelset'
          = LabelSet.add (absolute_address addr insn.Insn.read_operands.(0))
			 labelset in
	LabelSet.add (Int32.add addr 4l) labelset'
      with Not_PC_relative -> labelset
      end
  | _ -> labelset

let code_for_sym section mapping_syms sym =
  let start_offset = Int32.sub sym.st_value
			       shdr_arr.(sym.st_shndx).sh_addr
  and length = (Int32.to_int sym.st_size + 3) / 4 in
  let sym_bits = Bitstring.dropbits (8 * (Int32.to_int start_offset)) section in
  (* First pass: find labels.  *)
  let labelset = ref LabelSet.empty in
  for i = 0 to length - 1 do
    let insn_addr = Int32.add sym.st_value (Int32.of_int (i * 4)) in
    let map = Mapping.mapping_for_addr mapping_syms strtab insn_addr in
    match map with
      Mapping.ARM ->
        let decoded
	  = Decode_arm.decode_insn (Bitstring.dropbits (i * 32) sym_bits) in
        Printf.printf "%lx : %s\n" insn_addr (Mapping.string_of_mapping map);
	labelset := targets insn_addr decoded !labelset;
    | _ -> ()
  done;
  LabelSet.iter (fun targ -> Printf.printf "  label: %lx\n" targ) !labelset;
  (* Second pass: find basic blocks.  *)
  let seq_start = ref None
  and seq = ref Deque.empty in
  let seq_hash = Hashtbl.create 10 in
  let finish_seq () =
    begin match !seq_start with
      None -> ()
    | Some start_addr -> Hashtbl.add seq_hash start_addr !seq
    end;
    seq := Deque.empty;
    seq_start := None in
  for i = 0 to length - 1 do
    let insn_addr = Int32.add sym.st_value (Int32.of_int (i * 4)) in
    if LabelSet.mem insn_addr !labelset then begin
      Printf.printf "finishing sequence at addr: %lx\n" insn_addr;
      finish_seq ()
    end;
    let map = Mapping.mapping_for_addr mapping_syms strtab insn_addr in
    match map with
      Mapping.ARM ->
        if !seq_start = None then
	  seq_start := Some insn_addr;
	let decoded
	  = Decode_arm.decode_insn (Bitstring.dropbits (i * 32) sym_bits) in
	seq := Deque.snoc !seq decoded
    | _ ->
      finish_seq ()
  done;
  finish_seq ();
  seq_hash

module BS = Ir.IrBS

let bs_of_code_hash symbols code_hash =
  let idx = ref 0 in
  let ht = Hashtbl.create 10 in
  let blockseq = Hashtbl.fold
    (fun addr code bseq ->
      let irblock = Insn_to_ir.convert_block symbols addr code in
      Hashtbl.add ht addr !idx;
      incr idx;
      BS.cons irblock bseq)
    code_hash
    BS.empty in
  blockseq, ht

let code_for_named_sym section symbols mapping_syms strtab symname =
  let sym = Symbols.find_named_symbol symbols strtab symname in
  code_for_sym section mapping_syms sym

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

let mapping_syms = Mapping.get_mapping_symbols elfbits ehdr shdr_arr strtab
					       symbols ".text"

let code () =
  code_for_named_sym text symbols mapping_syms strtab "main"

let _ = code ()
