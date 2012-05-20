open Elfreader
open Dwarfreader
open Dwarfprint
open Binary_info

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
  | Insn.Bx
  | Insn.Conditional (_, Insn.B)
  | Insn.Conditional (_, Insn.Bl)
  | Insn.Conditional (_, Insn.Bx) ->
      let labelset' = LabelSet.add (Int32.add addr 4l) labelset in
      begin try
	LabelSet.add (absolute_address addr insn.Insn.read_operands.(0))
		     labelset'
      with Not_PC_relative -> labelset'
      end
  | Insn.Conditional (_, _) ->
      LabelSet.add (Int32.add addr 4l) labelset
  | _ -> labelset

let code_for_sym binf section mapping_syms sym =
  let start_offset = Int32.sub sym.st_value
			       binf.shdr_arr.(sym.st_shndx).sh_addr
  and length = (Int32.to_int sym.st_size + 3) / 4 in
  let sym_bits = Bitstring.dropbits (8 * (Int32.to_int start_offset)) section in
  (* First pass: find labels.  *)
  let labelset = ref LabelSet.empty in
  for i = 0 to length - 1 do
    let insn_addr = Int32.add sym.st_value (Int32.of_int (i * 4)) in
    let map = Mapping.mapping_for_addr mapping_syms binf.strtab insn_addr in
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
    let map = Mapping.mapping_for_addr mapping_syms binf.strtab insn_addr in
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
module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let eabi_pre_prologue ft real_entry_point =
  let insns =
    [C.Set (C.Reg (CT.Hard_reg 0), C.Nullary Irtypes.Arg_in);
     C.Set (C.Reg (CT.Hard_reg 1), C.Nullary Irtypes.Arg_in);
     C.Set (C.Reg (CT.Hard_reg 2), C.Nullary Irtypes.Arg_in);
     C.Set (C.Reg (CT.Hard_reg 3), C.Nullary Irtypes.Arg_in);
     C.Set (C.Reg (CT.Hard_reg 4), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 5), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 6), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 7), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 8), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 9), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 10), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 11), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 12), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Hard_reg 13), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Hard_reg 14), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Hard_reg 15), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Status Irtypes.CondFlags), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Status Irtypes.NZFlags), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Status Irtypes.Carry), C.Nullary Irtypes.Special)] in
  let cs = CS.of_list insns in
  let cs = Insn_to_ir.add_incoming_args ft cs in
  let cs = CS.snoc cs (C.Control (C.Jump real_entry_point)) in
  Block.make_block "entry block" cs

let eabi_post_epilogue () =
  let insns =
    [C.Set (C.Entity CT.Arg_out, C.Reg (CT.Hard_reg 0));
     C.Set (C.Entity CT.Arg_out, C.Reg (CT.Hard_reg 1));
     C.Set (C.Entity CT.Arg_out, C.Reg (CT.Hard_reg 2));
     C.Set (C.Entity CT.Arg_out, C.Reg (CT.Hard_reg 3));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 4));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 5));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 6));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 7));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 8));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 9));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 10));
     C.Set (C.Entity CT.Caller_restored, C.Reg (CT.Hard_reg 11));
     C.Control C.Virtual_exit] in
  let cs = CS.of_list insns in
  Block.make_block "exit block" cs

let cons_and_add_to_index blk bseq ht blockref idx =
  Hashtbl.add ht blockref !idx;
  incr idx;
  BS.cons blk bseq

let bs_of_code_hash ft binf code_hash entry_pt =
  let idx = ref 0 in
  let ht = Hashtbl.create 10 in
  let bseq_cons blk_id blk bseq =
    cons_and_add_to_index blk bseq ht blk_id idx in
  let blockseq = Hashtbl.fold
    (fun addr code bseq ->
      let block_id = Irtypes.BlockAddr addr in
      Insn_to_ir.convert_block binf block_id bseq bseq_cons addr code
			       code_hash)
    code_hash
    BS.empty in
  let pre_prologue_blk = eabi_pre_prologue ft entry_pt
  and virtual_exit = eabi_post_epilogue () in
  let with_entry_pt
    = bseq_cons Irtypes.Virtual_entry pre_prologue_blk blockseq in
  let with_exit_pt
    = bseq_cons Irtypes.Virtual_exit virtual_exit with_entry_pt in
  BS.rev with_exit_pt, ht

let code_for_named_sym binf section symbols mapping_syms strtab symname =
  let sym = Symbols.find_named_symbol symbols strtab symname in
  code_for_sym binf section mapping_syms sym

(*let debug_info_ptr = ref remaining_debug_info

let fetch_die () =
  let die_tree, die_hash, next_die = parse_die_for_cu !debug_info_ptr
				     ~length:debug_info_len
				     ~abbrevs ~addr_size:cu_header.address_size
				     ~string_sec:debug_str_sec in
  debug_info_ptr := next_die;
  die_tree, die_hash *)

(*let _ =
  let x, h = fetch_die () in
  print_all_dies x h*)

(* Next, we need to decode .debug_line!  *)

let print_blockseq_dfsinfo bseq =
  for i = 0 to Array.length bseq - 1 do
    let blk = bseq.(i) in
    Printf.printf "blk %d, id '%s', dfnum %d, pred [%s], succ [%s], parent %s, idom %s, idomchild [%s], domfront [%s]\n"
      i
      blk.Block.id
      blk.Block.dfnum
      (String.concat ", " 
	(List.map
	  (fun node -> string_of_int (node.Block.dfnum))
	  blk.Block.predecessors))
      (String.concat ", " 
	(List.map
	  (fun node -> string_of_int (node.Block.dfnum))
	  blk.Block.successors))
      (match blk.Block.parent with
	None -> "none"
      | Some p -> string_of_int p.Block.dfnum)
      (match blk.Block.idom with
	None -> "none"
      | Some idom -> string_of_int idom)
      (String.concat "," (List.map
        (fun node -> string_of_int node)
	blk.Block.idomchild))
      (String.concat "," (List.map
        (fun node -> string_of_int node)
	blk.Block.domfront))
  done

let dump_blockseq bs =
  Array.iter
    (fun block ->
      Printf.printf "block id \"%s\":\n" block.Block.id;
      Printf.printf "%s\n" (Ir.Ir.string_of_codeseq block.Block.code))
    bs

(*let mapping_syms = Mapping.get_mapping_symbols elfbits ehdr shdr_arr strtab
					       symbols ".text"*)

module IrDfs = Dfs.Dfs (Ir.IrCT) (Ir.IrCS) (Ir.IrBS)
module IrDominator = Dominator.Dominator (Ir.IrBS)
module IrPhiPlacement = Phi.PhiPlacement (Ir.IrCT) (Ir.IrCS) (Ir.IrBS)

let add_stackvars_to_entry_block blk_arr entry_pt_ref regset =
  let code = blk_arr.(entry_pt_ref).Block.code in
  let code' = IrPhiPlacement.R.fold
    (fun stackvar code ->
      CS.cons (C.Set (C.Reg stackvar, C.Nullary Irtypes.Arg_in)) code)
    regset
    code in
  blk_arr.(entry_pt_ref).Block.code <- code'

(*let binf = open_file "libGLESv2.so"*)
let binf = open_file "foo"

let go symname =
  let sym = Symbols.find_named_symbol binf.symbols binf.strtab symname in
  let entry_point = sym.Elfreader.st_value in
  let entry_point_ba = Irtypes.BlockAddr entry_point in
  let code = code_for_sym binf binf.text binf.mapping_syms sym in
  let cu_offset_for_sym = cu_offset_for_address binf entry_point in
  let cu = Hashtbl.find binf.cu_hash cu_offset_for_sym in
  let die = Hashtbl.find cu.ci_dieaddr entry_point in
  let ft = Function.function_type symname die cu.ci_dietab in
  let blockseq, ht = bs_of_code_hash ft binf code entry_point_ba in
  let entry_point_ref = Hashtbl.find ht entry_point_ba in
  Printf.printf "entry point %lx, ref %d\n" entry_point entry_point_ref;
  IrDfs.pred_succ ~whole_program:false blockseq ht Irtypes.Virtual_exit;
  IrDfs.dfs blockseq ht Irtypes.Virtual_entry;
  let blk_arr = IrDfs.blockseq_to_dfs_array blockseq in
  Printf.printf "--- after doing DFS ---\n";
  print_blockseq_dfsinfo blk_arr;
  flush stdout;
  IrDominator.dominators blk_arr;
  IrDominator.computedf blk_arr;
  Printf.printf "--- after computing dominators ---\n";
  print_blockseq_dfsinfo blk_arr;
  Printf.printf "--- SSA conversion (1) ---\n";
  let regset = IrPhiPlacement.place blk_arr in
  IrPhiPlacement.rename blk_arr 0 regset;
  Printf.printf "after SSA conversion:\n";
  dump_blockseq blk_arr;
  Printf.printf "--- gather info (1) ---\n";
  let inforec = Typedb.create_info () in
  Typedb.gather_info blk_arr inforec;
  Printf.printf "--- minipool resolution ---\n";
  let blk_arr' =
    Minipool.minipool_resolve binf.elfbits binf.ehdr binf.shdr_arr binf.symbols
			      binf.mapping_syms binf.strtab blk_arr inforec in
  dump_blockseq blk_arr';
  Printf.printf "--- sp tracking ---\n";
  Sptracking.sp_track blk_arr';
  dump_blockseq blk_arr';
  Printf.printf "--- SSA conversion (2) ---\n";
  let regset2 = IrPhiPlacement.place blk_arr' in
  (*add_stackvars_to_entry_block blk_arr' entry_point_ref regset2;*)
  IrPhiPlacement.rename blk_arr' 0 regset2;
  dump_blockseq blk_arr';
  Printf.printf "--- gather info (2) ---\n";
  Typedb.gather_info blk_arr' inforec;
  Typedb.print_info inforec.Typedb.infotag;
  Typedb.print_implied_info inforec.Typedb.implications;
  Printf.printf "--- eliminate phi nodes ---\n";
  IrPhiPlacement.eliminate blk_arr';
  dump_blockseq blk_arr'

(*let _ = go "blah"*)

let pubnames = Dwarfreader.parse_all_pubname_data binf.debug_pubnames

let debug_inf =
  List.map
    (fun (hdr, contents) ->
      let debug_inf_for_hdr =
        offset_section binf.debug_info hdr.pn_debug_info_offset in
      let cu_header, after_cu_hdr = parse_comp_unit_header debug_inf_for_hdr in
      let debug_abbr_offset = cu_header.debug_abbrev_offset in
      let debug_abbr = offset_section binf.debug_abbrev debug_abbr_offset in
      let abbrevs = parse_abbrevs debug_abbr in
      let _, die_hash, _ =
        parse_die_for_cu after_cu_hdr
	  ~length:(Bitstring.bitstring_length debug_inf_for_hdr)
	  ~abbrevs:abbrevs ~addr_size:cu_header.address_size
	  ~string_sec:binf.debug_str_sec in
      (*Hashtbl.add binf.cu_hash hdr.pn_debug_info_offset die_hash;*)
      List.map
	(fun (offset, name) ->
	  (*let die_bits = offset_section debug_inf_for_hdr offset in*)
	  let die = Hashtbl.find die_hash (Int32.to_int offset) in
	  (*parse_die_and_children die_bits
	    ~abbrevs:abbrevs ~addr_size:cu_header.address_size
	    ~string_sec:debug_str_sec in *)
	  (*Format.printf "debug info for '%s':@," name;
	  print_die die die_hash;*)
	  name, debug_inf_for_hdr, abbrevs, die, die_hash)
	contents)
    pubnames

(*let (name, die_bits, abbrevs, die, die_hash) =
  List.nth (List.nth debug_inf 1) 3*)
  (*Function.function_type name die_bits abbrevs die die_hash*)

(*let ft = Function.function_type name die die_hash*)

(*let ft = Ctype.resolve_type (List.hd a) die_hash*)

(*let try_all =
  List.map
    (fun nd_list ->
      List.map
        (fun (name, _) ->
	  try
	    Printf.printf "Trying '%s'\n" name;
	    go name;
	    Printf.printf "*** SUCCESS! ***\n"
	  with _ ->
	    Printf.printf "failed!\n"
	    )
	nd_list)
    debug_inf
*)
