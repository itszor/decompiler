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
  match insn.Insn.opcode with
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
        Log.printf 3 "%lx : %s\n" insn_addr (Mapping.string_of_mapping map);
	if decoded.Insn.opcode = Insn.BAD then
	  Log.printf 1 "Didn't decode insn at %lx successfully.\n" insn_addr;
	labelset := targets insn_addr decoded !labelset;
    | _ -> ()
  done;
  LabelSet.iter (fun targ -> Log.printf 3 "  label: %lx\n" targ) !labelset;
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
      Log.printf 3 "finishing sequence at addr: %lx\n" insn_addr;
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

let eabi_pre_prologue ft start_addr inforec real_entry_point =
  let insns =
    [(*C.Set (C.Reg (CT.Hard_reg 0), C.Nullary Irtypes.Arg_in);
     C.Set (C.Reg (CT.Hard_reg 1), C.Nullary Irtypes.Arg_in);
     C.Set (C.Reg (CT.Hard_reg 2), C.Nullary Irtypes.Arg_in);
     C.Set (C.Reg (CT.Hard_reg 3), C.Nullary Irtypes.Arg_in);*)
     C.Set (C.Reg (CT.Hard_reg 4), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 5), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 6), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 7), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 8), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 9), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 10), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 11), C.Nullary Irtypes.Caller_saved);
     C.Set (C.Reg (CT.Hard_reg 12), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Hard_reg 13), C.Nullary Irtypes.Incoming_sp);
     C.Set (C.Reg (CT.Hard_reg 14), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Hard_reg 15), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Status Irtypes.CondFlags), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Status Irtypes.NZFlags), C.Nullary Irtypes.Special);
     C.Set (C.Reg (CT.Status Irtypes.Carry), C.Nullary Irtypes.Special)] in
  let cs = CS.of_list insns in
  let cs =
    if false then
      Insn_to_ir.add_incoming_args ft cs
    else
      Insn_to_ir.add_real_incoming_args ft start_addr inforec cs in
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

let bs_of_code_hash ft binf inforec code_hash start_addr entry_pt =
  let idx = ref 0 in
  let ht = Hashtbl.create 10 in
  let bseq_cons blk_id blk bseq =
    cons_and_add_to_index blk bseq ht blk_id idx in
  let blockseq = Hashtbl.fold
    (fun addr code bseq ->
      let block_id = Irtypes.BlockAddr addr in
      Insn_to_ir.convert_block binf inforec block_id bseq bseq_cons addr code
			       code_hash)
    code_hash
    BS.empty in
  let pre_prologue_blk = eabi_pre_prologue ft start_addr inforec entry_pt
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
    Log.printf 3 "blk %d, id '%s', dfnum %d, pred [%s], succ [%s], parent %s, idom %s, idomchild [%s], domfront [%s]\n"
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
  BS.iter
    (fun block ->
      Log.printf 3 "block id \"%s\":\n" block.Block.id;
      Log.printf 3 "%s\n" (Ir.Ir.string_of_codeseq block.Block.code))
    bs

let dump_blockarr bs =
  Array.iter
    (fun block ->
      Log.printf 3 "block id \"%s\":\n" block.Block.id;
      Log.printf 3 "%s\n" (Ir.Ir.string_of_codeseq block.Block.code))
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
      CS.cons (C.Set (C.Reg stackvar,
		      C.Nullary (Irtypes.Declaration Ctype.C_int))) code)
    regset
    code in
  blk_arr.(entry_pt_ref).Block.code <- code'

let strip_ids blk_arr =
  Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt -> C.strip_ids stmt)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr

let graphviz blk_arr =
  let fh = open_out "func.gv" in
  Printf.fprintf fh "digraph func {\n";
  for i = 0 to Array.length blk_arr - 1 do
    Printf.fprintf fh "n%d [label=\"%s\"];\n" i blk_arr.(i).Block.id;
    List.iter
      (fun successor ->
	Printf.fprintf fh "n%d -> n%d;\n" i successor.Block.dfnum)
      blk_arr.(i).Block.successors;
    begin match blk_arr.(i).Block.idom with
      Some idom ->
        Printf.fprintf fh "n%d -> n%d [style=dotted];\n" i idom
    | None -> ()
    end
  done;
  Printf.fprintf fh "}\n";
  close_out fh

(*let binf = open_file "libGLESv2.so"*)
(*let binf = open_file "foo"*)
let binf = open_file "libglslcompiler.so"
(*let binf = open_file "tests/hello"*)
(*let binf = open_file "tests/rodata"*)
(*let binf = open_file "tests/fnargs"*)

let decompile_sym binf sym =
  let symname = Symbols.symbol_name sym binf.strtab in
  Log.printf 1 "*** decompiling '%s' ***\n" symname;
  let entry_point = sym.Elfreader.st_value in
  Log.printf 3 "entry point: %lx\n" entry_point;
  let entry_point_ba = Irtypes.BlockAddr entry_point in
  let code = code_for_sym binf binf.text binf.mapping_syms sym in
  let cu_offset_for_sym = cu_offset_for_address binf entry_point in
  let cu_inf = Hashtbl.find binf.cu_hash cu_offset_for_sym in
  let base_addr_for_cu = cu_inf.ci_baseaddr in
  Log.printf 2 "comp unit base addr: %lx\n" base_addr_for_cu;
  let die = Hashtbl.find cu_inf.ci_dieaddr entry_point in
  let ft =
    Function.function_type binf.debug_loc symname die cu_inf.ci_dietab
			   cu_inf.ci_ctypes
			   ~compunit_baseaddr:base_addr_for_cu in
  let vars = Function.function_vars die cu_inf.ci_dietab binf.debug_loc
	       ~compunit_baseaddr:base_addr_for_cu cu_inf.ci_ctypes in
  let inforec = Typedb.create_info () in
  let blockseq, ht =
    bs_of_code_hash ft binf inforec code entry_point entry_point_ba in
  Log.printf 2 "--- initial blockseq ---\n";
  dump_blockseq blockseq;
  let entry_point_ref = Hashtbl.find ht entry_point_ba in
  Log.printf 3 "entry point %lx, ref %d\n" entry_point entry_point_ref;
  Log.printf 2 "--- find & repair jump tables ---\n";
  let blockseq =
    Jumptable.repair_jumptables binf binf.text blockseq ht sym in
  dump_blockseq blockseq;
  Log.printf 2 "--- build DFS graph ---\n";
  IrDfs.pred_succ ~whole_program:false blockseq ht Irtypes.Virtual_exit;
  IrDfs.dfs blockseq ht Irtypes.Virtual_entry;
  let blk_arr = IrDfs.blockseq_to_dfs_array blockseq in
  Log.printf 2 "--- after doing DFS ---\n";
  print_blockseq_dfsinfo blk_arr;
  flush stdout;
  IrDominator.dominators blk_arr;
  IrDominator.computedf blk_arr;
  Log.printf 2 "--- after computing dominators ---\n";
  print_blockseq_dfsinfo blk_arr;
  graphviz blk_arr;
  Log.printf 2 "--- SSA conversion (1) ---\n";
  let regset = IrPhiPlacement.place blk_arr in
  IrPhiPlacement.rename blk_arr 0 regset;
  dump_blockarr blk_arr;
  (* Insert type info for function's locals here.  *)
  Log.printf 2 "--- gather info (1) ---\n";
  Typedb.gather_info blk_arr inforec;
  Log.printf 2 "--- strip ids ---\n";
  let blk_arr = strip_ids blk_arr in
  Log.printf 2 "--- minipool resolution ---\n";
  let blk_arr' =
    Minipool.minipool_resolve binf.elfbits binf.ehdr binf.shdr_arr binf.symbols
			      binf.mapping_syms binf.strtab blk_arr inforec
			      cu_inf.ci_ctypes in
  dump_blockarr blk_arr';
  (*Log.printf 1 "--- sp tracking ---\n";
  let sp_var_set = Sptracking.sp_track blk_arr' vars cu_inf.ci_ctypes in
  add_stackvars_to_entry_block blk_arr' 0 sp_var_set;
  dump_blockarr blk_arr';*)
  Log.printf 2 "--- gather sp refs ---\n";
  let stack_coverage =
    Ptrtracking.find_stack_references blk_arr' inforec vars cu_inf.ci_ctypes in
  Log.printf 2 "--- ptr tracking ---\n";
  let blk_arr', sp_var_set =
    Ptrtracking.pointer_tracking blk_arr' inforec vars cu_inf.ci_ctypes in
  add_stackvars_to_entry_block blk_arr' 0 sp_var_set;
  dump_blockarr blk_arr';
  Log.printf 2 "--- rewrite sp refs ---\n";
  let blk_arr', sp_ref_set =
    Ptrtracking.replace_stack_references blk_arr' stack_coverage vars inforec in
  add_stackvars_to_entry_block blk_arr' 0 sp_ref_set;
  dump_blockarr blk_arr';
  Log.printf 2 "--- SSA conversion (2) ---\n";
  let regset2 = IrPhiPlacement.place blk_arr' in
  IrPhiPlacement.rename blk_arr' 0 regset2;
  dump_blockarr blk_arr';
  Log.printf 2 "--- gather info (2) ---\n";
  Typedb.gather_info blk_arr' inforec;
  Typedb.print_info inforec.Typedb.infotag;
  Typedb.print_implied_info inforec.Typedb.implications;
  Log.printf 2 "--- slicing rodata ---\n";
  let rodata_sec = get_section_number binf.elfbits binf.ehdr binf.shdr_arr
				      ".rodata" in
  Slice_section.slice blk_arr' binf.rodata_sliced
    binf.shdr_arr.(rodata_sec).sh_addr ".rodata" symname;
  Log.printf 2 "--- removing prologue/epilogue code ---\n";
  let blk_arr'' = Ce.remove_prologue_and_epilogue blk_arr' in
  dump_blockarr blk_arr'';
  Log.printf 2 "--- eliminate phi nodes ---\n";
  IrPhiPlacement.eliminate blk_arr'';
  dump_blockarr blk_arr'';
  (*stack_coverage*)
  blk_arr''

let go symname =
  let sym = Symbols.find_named_symbol binf.symbols binf.strtab symname in
  decompile_sym binf sym

(*let really_go () =
  Log.loglevel := 4;
  (*go "InitAccumUSECodeBlocks"*)
  (*;go "AddComparisonToUFCode"*)
  (*go "ProcessICInstIFNOT"*)
  let blk_arr1 = go "main" in
  let blk_arr2 = go "main2" in
  let rodata_sec = get_section_number binf.elfbits binf.ehdr binf.shdr_arr
				      ".rodata" in
  Slice_section.symbols binf.rodata_sliced binf.symbols binf.strtab rodata_sec;
  Log.loglevel := 4;
  let blk_arr1' =
    Resolve_section.resolve blk_arr1 binf.rodata binf.rodata_sliced in
  dump_blockarr blk_arr1';
  let blk_arr2' =
    Resolve_section.resolve blk_arr2 binf.rodata binf.rodata_sliced in
  dump_blockarr blk_arr2'*)

(*let _ = really_go ()*)

(*let x =
  go "ProcessICInstIFNOT"*)
  (*go "main2"*)

let continue_after_error = ref false

let find_sym_and_try_decompile binf sym_addr fun_select =
  let sym = Symbols.find_symbol_by_addr
    ~filter:(fun sym -> Symbols.symbol_type sym = Symbols.STT_FUNC)
    binf.symbols
    sym_addr in
  try
    let name = Symbols.symbol_name sym binf.strtab in
    if fun_select name then begin
      ignore (decompile_sym binf sym);
      Log.printf 1 "PASS\n"
    end
  with x ->
    if not !continue_after_error then
      match x with
        Not_found ->
	  Printf.fprintf stderr "Not found\n";
	  failwith "Not found"
      | _ -> raise x
    else
      Log.printf 1 "FAIL\n"

(* Scan the toplevel DIEs defined in a CU.  *)

let scan_dietab_cu binf die fun_select =
  let rec scan die =
    match die with
      Die_tree ((DW_TAG_subprogram, attrs), children, sibl) ->
        begin try
	  let lowpc = get_attr_address attrs DW_AT_low_pc in
	  ignore (find_sym_and_try_decompile binf lowpc fun_select)
	with Not_found -> ()
	end;
	scan sibl
    | Die_node ((DW_TAG_subprogram, attrs), sibl) ->
        begin try
	  let lowpc = get_attr_address attrs DW_AT_low_pc in
	  ignore (find_sym_and_try_decompile binf lowpc fun_select)
	with Not_found -> ()
	end;
	scan sibl
    | Die_tree ((_, attrs), children, sibl) ->
	scan sibl
    | Die_node ((_, attrs), sibl) ->
	scan sibl
    | Die_empty -> () in
  scan die

let scan_dietab binf cu_inf cu_select fun_select =
  match cu_inf.ci_dies with
    Die_node ((DW_TAG_compile_unit, attrs), children) ->
      let name = get_attr_string attrs DW_AT_name in
      if cu_select name then begin
	Log.printf 1 "Compilation unit '%s'\n" name;
	scan_dietab_cu binf children fun_select
      end
  | _ -> ()

let scan_compunits ?(cu_select = fun _ -> true) ?(fun_select = fun _ -> true)
		   binf =
  Hashtbl.iter
    (fun cu_offset cu_inf ->
      scan_dietab binf cu_inf cu_select fun_select)
    binf.cu_hash

let decompile_something () =
  scan_compunits ~cu_select:((=) "glsl/icunroll.c")
    ~fun_select:((=) "ICUnrollLoopFOR") binf

(*let _ = decompile_something ()*)

(*let pubnames = Dwarfreader.parse_all_pubname_data binf.debug_pubnames

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
    pubnames*)

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
	    Log.printf 3 "Trying '%s'\n" name;
	    go name;
	    Log.printf 3 "*** SUCCESS! ***\n"
	  with _ ->
	    Log.printf 3 "failed!\n"
	    )
	nd_list)
    debug_inf
*)
