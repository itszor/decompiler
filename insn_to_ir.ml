(* Convert decoded INSN format into IR code type.  *)

open Insn

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let pseudo_num = ref 0

let flags_match a b =
  (List.sort compare a) = (List.sort compare b)

let create_pseudo () =
  let tmp = CT.Temp !pseudo_num in
  incr pseudo_num;
  tmp

let blk_num = ref 0

let create_blkref () =
  let blk = BS.BlockNum !blk_num in
  incr blk_num;
  blk

let convert_operand addr op =
  match op with
    Hard_reg 15 -> C.Entity (CT.PC (Int32.add addr 8l))
  | Hard_reg r -> C.Reg (CT.Hard_reg r)
  | VFP_sreg r -> C.Reg (CT.VFP_sreg r)
  | VFP_dreg r -> C.Reg (CT.VFP_dreg r)
  | FPSCR -> C.Reg (CT.Status CT.VFPFlags)
  | Immediate i -> C.Immed i
  | Converted already -> already
  | _ -> failwith "convert_operand"

let convert_maybe_pc_operand op =
  match op with
    Hard_reg 15 -> C.Reg (create_pseudo ()), true
  | Hard_reg r -> C.Reg (CT.Hard_reg r), false
  | _ -> failwith "convert_maybe_pc_operand"

let convert_mov addr insn =
  let convert_operand = convert_operand addr in
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0) in
    C.Set (dst, op1)
  end else
    C.Nullary (CT.Untranslated)

let convert_mvn addr insn =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand addr insn.write_operands.(0)
    and op1 = convert_operand addr insn.read_operands.(0) in
    C.Set (dst, C.Unary (CT.Not, op1))
  end else
    C.Nullary (CT.Untranslated)

let convert_binop addr opcode insn ilist =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst, loads_pc = convert_maybe_pc_operand insn.write_operands.(0)
    and op1 = convert_operand addr insn.read_operands.(0)
    and op2 = convert_operand addr insn.read_operands.(1) in
    if loads_pc then
      let ilist' = CS.snoc ilist (C.Set (dst, C.Binary (opcode, op1, op2))) in
      CS.snoc ilist' (C.Control (C.CompJump (dst, [])))
    else
      CS.snoc ilist (C.Set (dst, C.Binary (opcode, op1, op2)))
  end else
    CS.snoc ilist (C.Nullary (CT.Untranslated))

let convert_bic addr insn ilist =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let op2 = convert_operand addr insn.read_operands.(1) in
    let new_reads = Array.copy insn.read_operands in
    new_reads.(1) <- Converted (C.Unary (CT.Not, op2));
    convert_binop addr CT.And { insn with read_operands = new_reads } ilist
  end else
    CS.snoc ilist (C.Nullary (CT.Untranslated))

let convert_rsb addr insn =
  let convert_operand = convert_operand addr in
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (dst, C.Binary (CT.Sub, op2, op1))
  end else
    C.Nullary (CT.Untranslated)

let convert_mla addr insn =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand addr insn.write_operands.(0)
    and op1 = convert_operand addr insn.read_operands.(0)
    and op2 = convert_operand addr insn.read_operands.(1)
    and op3 = convert_operand addr insn.read_operands.(2) in
    C.Set (dst, C.Trinary (CT.Mla, op1, op2, op3))
  end else
    C.Nullary (CT.Untranslated)

let convert_carry_in_op addr opcode insn =
  let convert_operand = convert_operand addr in
  if insn.write_flags = [] && insn.read_flags = [C] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (dst, C.Trinary (opcode, op1, op2,
	   C.Reg (CT.Status CT.Carry)))
  end else
    C.Nullary (CT.Untranslated)

let make_shifted_operand shift operand amount =
  let op =
    match shift with
      Lsl ->
	C.Binary (CT.Lsl, operand, amount)
    | Lsr ->
	C.Binary (CT.Lsr, operand, amount)
    | Asr ->
	C.Binary (CT.Asr, operand, amount)
    | Ror ->
	C.Binary (CT.Ror, operand, amount)
    | Rrx ->
	C.Binary (CT.Rrx, operand, amount) in
  Converted op

let convert_address addr ainf insn base index =
  match ainf.addr_mode with
    Base_plus_imm
  | Base_plus_reg -> C.Binary (CT.Add, base, index)
  | Base_minus_reg -> C.Binary (CT.Sub, base, index)
  | Base_plus_shifted_reg shift ->
      let num_reads = Array.length insn.read_operands in
      let shift_amt = convert_operand addr insn.read_operands.(num_reads - 1) in
      let shifted_index = make_shifted_operand shift index shift_amt in
      C.Binary (CT.Add, base, convert_operand addr shifted_index)
  | Base_minus_shifted_reg shift ->
      let num_reads = Array.length insn.read_operands in
      let shift_amt = convert_operand addr insn.read_operands.(num_reads - 1) in
      let shifted_index = make_shifted_operand shift index shift_amt in
      C.Binary (CT.Sub, base, convert_operand addr shifted_index)

let convert_load addr ainf insn access ilist =
  let base = convert_operand addr insn.read_operands.(0)
  and index = convert_operand addr insn.read_operands.(1) in
  let conv_addr = convert_address addr ainf insn base index
  and dst, loads_pc = convert_maybe_pc_operand insn.write_operands.(0) in
  let ilist' = if ainf.pre_modify then begin
    let ilist = CS.snoc ilist (C.Set (dst, C.Load (access, conv_addr))) in
    if ainf.writeback then
      let w_base = convert_operand addr insn.write_operands.(1) in
      CS.snoc ilist (C.Set (w_base, conv_addr))
    else
      ilist
  end else begin
    assert ainf.writeback;
    let w_base = convert_operand addr insn.write_operands.(1) in
    let ilist = CS.snoc ilist (C.Set (dst, C.Load (access, base))) in
    CS.snoc ilist (C.Set (w_base, conv_addr))
  end in
  if loads_pc then
    CS.snoc ilist' (C.Control (C.CompJump_ext (CT.Branch_exchange, dst)))
  else
    ilist'

let convert_store addr ainf insn access ilist =
  let base = convert_operand addr insn.read_operands.(1)
  and index = convert_operand addr insn.read_operands.(2) in
  let conv_addr = convert_address addr ainf insn base index
  and src = convert_operand addr insn.read_operands.(0) in
  if ainf.pre_modify then begin
    let ilist = CS.snoc ilist (C.Store (access, conv_addr, src)) in
    if ainf.writeback then
      let w_base = convert_operand addr insn.write_operands.(0) in
      CS.snoc ilist (C.Set (w_base, conv_addr))
    else
      ilist
  end else begin
    assert ainf.writeback;
    let w_base = convert_operand addr insn.write_operands.(0) in
    let ilist = CS.snoc ilist (C.Store (access, base, src)) in
    CS.snoc ilist (C.Set (w_base, conv_addr))
  end

(* For LDM:
   read operand is: [base reg]
   write operands are: [<optional writeback reg,> reg list...]
*)

let convert_ldm addr minf insn ilist =
  let offset = ref 0 in
  begin match minf.before, minf.increment with
    false, _ -> offset := 0
  | true, false -> offset := -4
  | true, true -> offset := 4
  end;
  let base_reg = convert_operand addr insn.read_operands.(0) in
  let ilist_r = ref ilist in
  let jump_to_tmp = ref None in
  let reglist_start = if minf.mm_writeback then 1 else 0 in
  for i = reglist_start to Array.length insn.write_operands - 1 do
    let addr' = C.Binary (CT.Add, base_reg,
			  C.Immed (Int32.of_int !offset)) in
    let reg, loads_pc = convert_maybe_pc_operand insn.write_operands.(i) in
    let load = C.Set (reg, C.Load (CT.Word, addr')) in
    ilist_r := CS.snoc !ilist_r load;
    if minf.increment then
      offset := !offset + 4
    else
      offset := !offset - 4;
    if loads_pc then
      jump_to_tmp := Some reg
  done;
  if minf.mm_writeback then begin
    let loaded_regs = Array.length insn.write_operands - reglist_start in
    let offset = if minf.increment then loaded_regs * 4 else -loaded_regs * 4 in
    let writeback = C.Set (base_reg,
			   C.Binary (CT.Add, base_reg,
				     C.Immed (Int32.of_int offset))) in
    ilist_r := CS.snoc !ilist_r writeback
  end;
  begin match !jump_to_tmp with
    None -> ()
  | Some tmp ->
      ilist_r := CS.snoc !ilist_r
		   (C.Control (C.CompJump_ext (CT.Branch_exchange, tmp)))
  end;
  !ilist_r

(* For STM:
   read operands are: [base reg, first reg in list, ..., last reg in list].
   write operands are: [] (empty list) or [base reg] for writeback.
*)

let convert_stm addr minf insn ilist =
  let offset = ref 0 in
  begin match minf.before, minf.increment with
    false, _ -> offset := 0
  | true, false -> offset := -4
  | true, true -> offset := 4
  end;
  let base_reg = convert_operand addr insn.read_operands.(0) in
  let ilist_r = ref ilist in
  for i = 1 to Array.length insn.read_operands - 1 do
    let addr' = C.Binary (CT.Add, base_reg,
			  C.Immed (Int32.of_int !offset)) in
    let store = C.Store (CT.Word, addr',
			 convert_operand addr insn.read_operands.(i)) in
    ilist_r := CS.snoc !ilist_r store;
    if minf.increment then
      offset := !offset + 4
    else
      offset := !offset - 4
  done;
  if minf.mm_writeback then begin
    let stored_regs = Array.length insn.read_operands - 1 in
    let offset = if minf.increment then stored_regs * 4 else -stored_regs * 4 in
    let writeback = C.Set (base_reg,
			   C.Binary (CT.Add, base_reg,
				     C.Immed (Int32.of_int offset))) in
    ilist_r := CS.snoc !ilist_r writeback
  end;
  !ilist_r

let convert_bx addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    Hard_reg r ->
      C.Control (C.CompJump_ext (CT.Branch_exchange, convert_operand addr dest))
  | _ -> failwith "unexpected bx operand"

let convert_condition cond =
  let code =
    match cond with
      Ne -> CT.Status_ne
    | Eq -> CT.Status_eq
    | Lt -> CT.Status_lt
    | Le -> CT.Status_le
    | Gt -> CT.Status_gt
    | Ge -> CT.Status_ge
    | Mi -> CT.Status_ltu
    | Pl -> CT.Status_geu
    | Hi -> CT.Status_gtu
    | Ls -> CT.Status_leu
    | Cc -> CT.Status_cc
    | Cs -> CT.Status_cs
    | Vc -> CT.Status_vc
    | Vs -> CT.Status_vs in
  C.Unary (code, C.Reg (CT.Status CT.CondFlags))

(* This is entirely wrong!  *)

let convert_cond_bx cond addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    Hard_reg r ->
      let falseblock = Int32.add addr 4l in
      C.Control (C.Branch (convert_condition cond,
			   BS.BlockAddr falseblock,
			   BS.BlockAddr falseblock))
  | _ -> failwith "unexpected bx operand"

let find_symbol symbols strtab addr =
  try
    let symbol = Symbols.find_symbol_by_addr symbols addr in
    let symname = Symbols.symbol_name symbol strtab in
    CT.Symbol (symname, symbol)
  with Not_found ->
    CT.Absolute addr

let stackregs_to_loads c =
  C.map
    (function
	C.Reg (CT.Stack x) ->
	  C.Protect (C.Load (CT.Word,
			     C.Binary (CT.Add, C.Reg (CT.Hard_reg 13),
				       C.Immed (Int32.of_int x))))
      | x -> x)
    c

let rec code_for_location loc =
  match loc with
    Locations.In x -> x
  | Locations.Parts partlist ->
      let sorted_parts =
        List.sort (fun (a, _, _) (b, _, _) -> compare a b) partlist in
      let rec build cursor parts =
        match parts with
	  [] -> []
	| (lo, size, code) :: remain ->
	    assert (lo == cursor);
	    (code_for_location code) :: build (lo + size) remain in
      let codeparts = build 0 sorted_parts in
      C.Concat (Array.of_list (List.rev codeparts))
  | Locations.Within_range _ -> failwith "unexpected within_range"

let fn_args callee_addr ft ct_for_cu =
  let accum = Eabi.make_arg_accum () in
  let args = Array.mapi
    (fun i typ ->
      let aloc = Eabi.eabi_arg_loc ft i accum ct_for_cu in
      stackregs_to_loads (code_for_location aloc))
    ft.Function.args in
  C.Nary (CT.Fnargs, Array.to_list args)

let add_incoming_args ft codeseq ct_for_cu =
  let accum = Eabi.make_arg_accum () in
  let args = Array.mapi
    (fun i _ ->
      let aloc = Eabi.eabi_arg_loc ft i accum ct_for_cu in
      code_for_location aloc)
    ft.Function.args in
  let cseq', _ = Array.fold_left
    (fun (cseq, argnum) argloc ->
      let insn =
        match argloc with
	  (* FIXME: CT.Word might not always be right. 
	     Bigger-than-word-sized arguments are not handled properly.  *)
	  C.Reg (CT.Stack x) ->
	    C.Store (CT.Word,
		     C.Binary (CT.Add, C.Reg (CT.Hard_reg 13),
			       C.Immed (Int32.of_int x)),
		     C.Entity (CT.Arg_var ft.Function.arg_names.(argnum)))
	| _ -> C.Set (argloc,
		      C.Entity (CT.Arg_var ft.Function.arg_names.(argnum))) in
      CS.snoc cseq insn, succ argnum)
    (codeseq, 0)
    args in
  if Eabi.hidden_struct_return ft ct_for_cu then
    CS.snoc cseq' (C.Set (C.Reg (CT.Hard_reg 0),
			  C.Nullary
			    (CT.Incoming_aggr_return ft.Function.return)))
  else
    cseq'

let fn_ret ft ct_for_cu =
  let loc_opt = Eabi.eabi_return_loc ft ct_for_cu in
  match loc_opt with
    Some loc -> Some (code_for_location loc)
  | None -> None

exception Calling of string
exception Dest_not_function

(* This is awful: a circular dependency!  Find a nicer solution...  *)
let symbol_for_plt_entry = ref (fun _ _ -> failwith "binding")

let try_function_call binf inforec dst_addr =
  let targ_sec = Elfreader.get_section_num_by_addr binf.Binary_info.elfbits
		   binf.Binary_info.ehdr binf.Binary_info.shdr_arr
		   dst_addr in
  let targ_sec_name = Elfreader.get_section_name binf.Binary_info.elfbits
			binf.Binary_info.ehdr binf.Binary_info.shdr_arr
			targ_sec in
  (* We should probably be looking at ELF flags here not section name!  *)
  match targ_sec_name with
    ".text" ->
      begin try
	let cu_for_dest = Binary_info.cu_offset_for_address binf dst_addr in
	let cu_inf = Hashtbl.find binf.Binary_info.cu_hash cu_for_dest in
	let sym =
	  begin try
	    Hashtbl.find cu_inf.Binary_info.ci_symtab dst_addr
	  with Not_found ->
	    raise Dest_not_function
	  end in
	let die = Hashtbl.find cu_inf.Binary_info.ci_dieaddr dst_addr in
	let symname = Symbols.symbol_name sym binf.Binary_info.strtab in
	(*let sym_or_addr = find_symbol binf.Binary_info.symbols
				      binf.Binary_info.strtab dst_addr in*)
	let fn_inf =
	  Function.function_type binf.Binary_info.debug_loc symname die
	    cu_inf.Binary_info.ci_dietab cu_inf.Binary_info.ci_ctypes
	    ~compunit_baseaddr:cu_inf.Binary_info.ci_baseaddr in
	let ct_sym = CT.Finf_sym (symname, fn_inf, sym) in
	let passes = fn_args dst_addr fn_inf cu_inf.Binary_info.ci_ctypes
	and returns = fn_ret fn_inf cu_inf.Binary_info.ci_ctypes in
	CT.EABI, ct_sym, passes, returns
      with Not_found ->
	(* No debug info for this one.  *)
	let sym = Symbols.find_symbol_by_addr
	  ~filter:(fun sym -> not (Mapping.is_mapping_symbol sym))
	  binf.Binary_info.symbols dst_addr in
	let symname = Symbols.symbol_name sym binf.Binary_info.strtab in
	CT.EABI, CT.Symbol (symname, sym), C.Nary (CT.Fnargs, []), None
      end
  | ".plt" ->
      let sym, sym_name =
	try
	  let sym = (!symbol_for_plt_entry) binf dst_addr in
	  let sym_name = Symbols.symbol_name sym binf.Binary_info.dynstr in
	  sym, sym_name
	with Not_found ->
	  List.hd binf.Binary_info.symbols,
	  Printf.sprintf "<plt@%lx>" dst_addr in
      begin try
	let ext_ctypes, fn_inf =
	  External.lookup_function binf.Binary_info.libs sym_name in
	CT.Plt_call, CT.Symbol (sym_name, sym),
	  fn_args dst_addr fn_inf ext_ctypes,
	  fn_ret fn_inf ext_ctypes
      with Not_found ->
        CT.Plt_call, CT.Symbol (sym_name, sym), C.Nary (CT.Fnargs, []),
	None
      end
  | x -> raise (Calling x)

let convert_bl binf inforec addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let ret_addr = BS.BlockAddr (Int32.add addr 4l) in
      let call_addr = Int32.add addr i in
      let abi, call_code, passes, returns =
        try_function_call binf inforec call_addr in
      begin match returns with
        None -> C.Call_ext (abi, call_code, passes)
      | Some r -> C.Set (r, C.Call_ext (abi, call_code, passes))
      end
  | _ -> failwith "unexpected bx operand"

let convert_cmp cmptype addr insn =
  if insn.read_flags = [] && flags_match insn.write_flags [C;V;N;Z] then begin
    let op1 = convert_operand addr insn.read_operands.(0)
    and op2 = convert_operand addr insn.read_operands.(1) in
    C.Set (C.Reg (CT.Status CT.CondFlags),
	   C.Binary (cmptype, op1, op2))
  end else
    C.Nullary (CT.Untranslated)

let convert_tst addr insn =
  let convert_operand = convert_operand addr in
  if insn.read_flags = [] && flags_match insn.write_flags [N;Z] then begin
    let op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (C.Reg (CT.Status CT.CondFlags),
	   C.Binary (CT.Tst, op1, op2))
  end else
    C.Nullary (CT.Untranslated)

let convert_bfx xtype addr insn =
  let op1 = convert_operand addr insn.read_operands.(0)
  and op2 = convert_operand addr insn.read_operands.(1)
  and op3 = convert_operand addr insn.read_operands.(2)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Trinary (xtype, op1, op2, op3))

let convert_bfi addr insn =
  let op1 = convert_operand addr insn.read_operands.(0)
  and op2 = convert_operand addr insn.read_operands.(1)
  and op3 = convert_operand addr insn.read_operands.(2)
  and op4 = convert_operand addr insn.read_operands.(3)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Nary (CT.Bfi, [op1; op2; op3; op4]))

(* FIXME: No rotates yet!  *)

let convert_xt xtype addr insn =
  let op = convert_operand addr insn.read_operands.(0)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Unary (xtype, op))

let convert_rr2f addr insn ilist =
  match insn.write_operands with
    [| VFP_dreg rm |] ->
      let insn = 
	C.Set (convert_operand addr insn.write_operands.(0),
	       C.Concat [| convert_operand addr insn.read_operands.(0);
			   convert_operand addr insn.read_operands.(1) |]) in
      CS.snoc ilist insn
  | [| VFP_sreg rm1; VFP_sreg rm2 |] ->
      let insn1 = C.Set (convert_operand addr insn.write_operands.(0),
			 convert_operand addr insn.read_operands.(0))
      and insn2 = C.Set (convert_operand addr insn.write_operands.(1),
			 convert_operand addr insn.read_operands.(1)) in
      let ilist' = CS.snoc ilist insn1 in
      CS.snoc ilist insn2
  | _ -> CS.snoc ilist (C.Nullary CT.Untranslated)

let convert_f2rr addr insn ilist =
  match insn.read_operands with
    [| VFP_dreg rm |] ->
      let insn =
        (* Leave this as a single instruction because we don't really want it
	   to be split -- it most likely represents a single transfer.
	   FIXME: Allow concat on the LHS instead?  *)
        C.Parallel
          [| C.Set (convert_operand addr insn.write_operands.(0),
		    C.Unary (CT.Dreg_lopart,
			     convert_operand addr insn.read_operands.(0)));
	     C.Set (convert_operand addr insn.write_operands.(1),
		    C.Unary (CT.Dreg_hipart,
			     convert_operand addr insn.read_operands.(0))) |] in
      CS.snoc ilist insn
  | [| VFP_sreg rm1; VFP_sreg rm2 |] ->
      let insn1 = C.Set (convert_operand addr insn.write_operands.(0),
			 convert_operand addr insn.read_operands.(0))
      and insn2 = C.Set (convert_operand addr insn.write_operands.(1),
			 convert_operand addr insn.read_operands.(1)) in
      let ilist' = CS.snoc ilist insn1 in
      CS.snoc ilist' insn2
  | _ -> CS.snoc ilist (C.Nullary CT.Untranslated)

let vfp_reg_size = function
    VFP_sreg _ -> 4
  | VFP_dreg _ -> 8
  | _ -> failwith "vfp_reg_size"

let vfp_reg_xfer = function
    VFP_sreg _ -> CT.Word
  | VFP_dreg _ -> CT.Dword
  | _ -> failwith "vfp_reg_xfer"

let convert_vstm addr minf insn ilist =
  let rsize = vfp_reg_size insn.read_operands.(1) in
  let xfer = vfp_reg_xfer insn.read_operands.(1) in
  let offset = ref 0 in
  begin match minf.before, minf.increment with
    false, _ -> offset := 0
  | true, false -> offset := -rsize
  | true, true -> offset := rsize
  end;
  let base_reg = convert_operand addr insn.read_operands.(0) in
  let ilist_r = ref ilist in
  for i = 1 to Array.length insn.read_operands - 1 do
    let addr' = C.Binary (CT.Add, base_reg,
			  C.Immed (Int32.of_int !offset)) in
    let store = C.Store (xfer, addr',
			 convert_operand addr insn.read_operands.(i)) in
    ilist_r := CS.snoc !ilist_r store;
    if minf.increment then
      offset := !offset + rsize
    else
      offset := !offset - rsize
  done;
  if minf.mm_writeback then begin
    let stored_regs = Array.length insn.read_operands - 1 in
    let offset = if minf.increment then stored_regs * rsize
		 else -stored_regs * rsize in
    let writeback = C.Set (base_reg,
			   C.Binary (CT.Add, base_reg,
				     C.Immed (Int32.of_int offset))) in
    ilist_r := CS.snoc !ilist_r writeback
  end;
  !ilist_r

let convert_vldm addr minf insn ilist =
  let reglist_start = if minf.mm_writeback then 1 else 0 in
  let rsize = vfp_reg_size insn.write_operands.(reglist_start) in
  let xfer = vfp_reg_xfer insn.write_operands.(reglist_start) in
  let offset = ref 0 in
  begin match minf.before, minf.increment with
    false, _ -> offset := 0
  | true, false -> offset := -rsize
  | true, true -> offset := rsize
  end;
  let base_reg = convert_operand addr insn.read_operands.(0) in
  let ilist_r = ref ilist in
  for i = reglist_start to Array.length insn.write_operands - 1 do
    let addr' = C.Binary (CT.Add, base_reg,
			  C.Immed (Int32.of_int !offset)) in
    let reg = convert_operand addr insn.write_operands.(i) in
    let load = C.Set (reg, C.Load (xfer, addr')) in
    ilist_r := CS.snoc !ilist_r load;
    if minf.increment then
      offset := !offset + rsize
    else
      offset := !offset - rsize
  done;
  if minf.mm_writeback then begin
    let loaded_regs = Array.length insn.write_operands - reglist_start in
    let offset = if minf.increment then loaded_regs * rsize
		 else -loaded_regs * rsize in
    let writeback = C.Set (base_reg,
			   C.Binary (CT.Add, base_reg,
				     C.Immed (Int32.of_int offset))) in
    ilist_r := CS.snoc !ilist_r writeback
  end;
  !ilist_r

let convert_vstr addr insn =
  let base = convert_operand addr insn.read_operands.(1)
  and offset = convert_operand addr insn.read_operands.(2)
  and stored_reg = convert_operand addr insn.read_operands.(0) in
  let store_type = vfp_reg_xfer insn.read_operands.(0) in
  C.Store (store_type, C.Binary (CT.Add, base, offset), stored_reg)

let convert_vldr addr insn =
  let base = convert_operand addr insn.read_operands.(0)
  and offset = convert_operand addr insn.read_operands.(1)
  and loaded_reg = convert_operand addr insn.write_operands.(0) in
  let load_type = vfp_reg_xfer insn.write_operands.(0) in
  C.Set (loaded_reg, C.Load (load_type, C.Binary (CT.Add, base, offset)))

let convert_vcvt ctype addr insn =
  let op = convert_operand addr insn.read_operands.(0)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Unary (ctype, op))

let convert_vcmp ctype addr insn =
  let op1 = convert_operand addr insn.read_operands.(0)
  and op2 = convert_operand addr insn.read_operands.(1)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Binary (ctype, op1, op2))

let convert_vmrs addr insn =
  let op1 = convert_operand addr insn.read_operands.(0) in
  if flags_match insn.write_flags [C;V;N;Z] then
    C.Set (C.Reg (CT.Status CT.CondFlags), op1)
  else
    let dst = convert_operand addr insn.write_operands.(0) in
    C.Set (dst, op1)

let convert_vfp_unop code addr insn =
  let op1 = convert_operand addr insn.read_operands.(0)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Unary (code, op1))

let convert_vfp_binop code addr insn =
  let op1 = convert_operand addr insn.read_operands.(0)
  and op2 = convert_operand addr insn.read_operands.(1)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Binary (code, op1, op2))

let convert_vfp_triop code addr insn =
  let op1 = convert_operand addr insn.read_operands.(0)
  and op2 = convert_operand addr insn.read_operands.(1)
  and op3 = convert_operand addr insn.read_operands.(2)
  and dst = convert_operand addr insn.write_operands.(0) in
  C.Set (dst, C.Trinary (code, op1, op2, op3))

let convert_cbranch cond addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let trueblock = BS.BlockAddr (Int32.add addr i)
      and falseblock = BS.BlockAddr (Int32.add addr 4l) in
      C.Control (C.Branch (convert_condition cond, trueblock, falseblock))
  | _ -> failwith "unexpected b<cond> operand"

let convert_branch binf inforec addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let dst_addr = Int32.add addr i in
      let no_arg = C.Nullary CT.Nop in
      begin try
        let abi, call_code, passes, _ =
          try_function_call binf inforec dst_addr in
	C.Control (C.TailCall_ext (abi, call_code, passes))
      with Dest_not_function ->
	C.Control (C.Jump (BS.BlockAddr (Int32.add addr i)))
      end
  | _ -> failwith "unexpected b operand"

exception Unsupported_opcode of Insn.opcode

let name_for_block_id = function
    BS.BlockAddr addr -> Printf.sprintf "block_for_addr_0x%lx" addr
  | BS.BlockNum n -> Printf.sprintf "block_num_%d" n
  | BS.Virtual_entry -> "virtual_entry"
  | BS.Virtual_exit -> "virtual_exit"

(* Start a new block, adding the insns for the previous block to the block
   sequence and adding it to the block index hashtbl.  If the insn list
   doesn't end with a control flow insn and CHAIN is set to a block id, adds a
   jump from the end of the old block to the new one.  Returns new blockseq.  *)

let finish_block block_id ?chain insnlist bseq bseq_cons =
  let insnlist' =
    if not (CS.is_empty insnlist) then begin
      if C.finishes_with_control insnlist then
	insnlist
      else begin
        match chain with
	  None -> insnlist
	| Some chain ->
	    let fallthru = C.Control (C.Jump chain) in
	    CS.snoc insnlist fallthru
      end
    end else begin
      match chain with
	None -> failwith "empty block and no chain?"
      | Some chain ->
	  let fallthru = C.Control (C.Jump chain) in
	  CS.snoc insnlist fallthru
    end in
  (*let name = name_for_block_id block_id in*)
  let blk = Block.make_block block_id insnlist' in
  bseq_cons block_id blk bseq

let rec convert_insn binf inforec addr insn ilist blk_id bseq bseq_cons =
  let ilist = CS.snoc ilist (C.Entity (CT.Insn_address addr)) in
  let append insn =
    CS.snoc ilist insn, blk_id, bseq
  and same_blk ilist =
    ilist, blk_id, bseq in
  match insn.opcode with
    Mov -> append (convert_mov addr insn)
  | Mvn -> append (convert_mvn addr insn)
  | Add -> same_blk (convert_binop addr CT.Add insn ilist)
  | Sub -> same_blk (convert_binop addr CT.Sub insn ilist)
  | And -> same_blk (convert_binop addr CT.And insn ilist)
  | Eor -> same_blk (convert_binop addr CT.Eor insn ilist)
  | Orr -> same_blk (convert_binop addr CT.Or insn ilist)
  | Bic -> same_blk (convert_bic addr insn ilist)
  | Mul -> same_blk (convert_binop addr CT.Mul insn ilist)
  | Mla -> append (convert_mla addr insn)
  | Rsb -> append (convert_rsb addr insn)
  | Adc -> append (convert_carry_in_op addr CT.Adc insn)
  | Sbc -> append (convert_carry_in_op addr CT.Sbc insn)
  | Cmp -> append (convert_cmp CT.Cmp addr insn)
  | Cmn -> append (convert_cmp CT.Cmn addr insn)
  | Tst -> append (convert_tst addr insn)
  | Ldr ainf -> same_blk (convert_load addr ainf insn CT.Word ilist)
  | Ldrb ainf -> same_blk (convert_load addr ainf insn CT.U8 ilist)
  | Str ainf -> same_blk (convert_store addr ainf insn CT.Word ilist)
  | Strb ainf -> same_blk (convert_store addr ainf insn CT.U8 ilist)
  | Ldrh ainf -> same_blk (convert_load addr ainf insn CT.U16 ilist)
  | Strh ainf -> same_blk (convert_store addr ainf insn CT.U16 ilist)
  | Ldrsh ainf -> same_blk (convert_load addr ainf insn CT.S16 ilist)
  | Ldrsb ainf -> same_blk (convert_load addr ainf insn CT.S8 ilist)
  | Strd ainf -> same_blk (convert_store addr ainf insn CT.Dword ilist)
  | Ldrd ainf -> same_blk (convert_load addr ainf insn CT.Dword ilist)
  | Ldm minf -> same_blk (convert_ldm addr minf insn ilist)
  | Stm minf -> same_blk (convert_stm addr minf insn ilist)
  | Ubfx -> append (convert_bfx CT.Ubfx addr insn)
  | Sbfx -> append (convert_bfx CT.Sbfx addr insn)
  | Bfi -> append (convert_bfi addr insn)
  | Uxtb -> append (convert_xt CT.Uxtb addr insn)
  | Sxtb -> append (convert_xt CT.Sxtb addr insn)
  | Uxth -> append (convert_xt CT.Uxth addr insn)
  | Sxth -> append (convert_xt CT.Sxth addr insn)
  | Vmov_rr2f -> same_blk (convert_rr2f addr insn ilist)
  | Vmov_f2rr -> same_blk (convert_f2rr addr insn ilist)
  | Vmov_f2r -> append (convert_mov addr insn)
  | Vmov_r2f -> append (convert_mov addr insn)
  | Vmov_imm -> append (convert_mov addr insn)
  | Vmov_reg -> append (convert_mov addr insn)
  | Vldm minf -> same_blk (convert_vldm addr minf insn ilist)
  | Vstm minf -> same_blk (convert_vstm addr minf insn ilist)
  | Vldr -> append (convert_vldr addr insn)
  | Vstr -> append (convert_vstr addr insn)
  | Vcvt_d2f -> append (convert_vcvt CT.Vcvt_d2f addr insn)
  | Vcvt_f2d -> append (convert_vcvt CT.Vcvt_f2d addr insn)
  | Vcvt_f2si -> append (convert_vcvt CT.Vcvt_f2si addr insn)
  | Vcvt_f2ui -> append (convert_vcvt CT.Vcvt_f2ui addr insn)
  | Vcvtr_f2si -> append (convert_vcvt CT.Vcvtr_f2si addr insn)
  | Vcvtr_f2ui -> append (convert_vcvt CT.Vcvtr_f2ui addr insn)
  | Vcvt_si2f -> append (convert_vcvt CT.Vcvt_si2f addr insn)
  | Vcvt_ui2f -> append (convert_vcvt CT.Vcvt_ui2f addr insn)
  | Vcmp -> append (convert_vcmp CT.Vcmp addr insn)
  | Vcmpe -> append (convert_vcmp CT.Vcmpe addr insn)
  | Vmrs -> append (convert_vmrs addr insn)
  | Vneg -> append (convert_vfp_unop CT.Vneg addr insn)
  | Vabs -> append (convert_vfp_unop CT.Vabs addr insn)
  | Vsqrt -> append (convert_vfp_unop CT.Vsqrt addr insn)
  | Vadd -> append (convert_vfp_binop CT.Vadd addr insn)
  | Vsub -> append (convert_vfp_binop CT.Vsub addr insn)
  | Vmul -> append (convert_vfp_binop CT.Vmul addr insn)
  | Vnmul -> append (convert_vfp_binop CT.Vnmul addr insn)
  | Vdiv -> append (convert_vfp_binop CT.Vdiv addr insn)
  | Vmla -> append (convert_vfp_triop CT.Vmla addr insn)
  | Vmls -> append (convert_vfp_triop CT.Vmls addr insn)
  | Vnmla -> append (convert_vfp_triop CT.Vnmla addr insn)
  | Vnmls -> append (convert_vfp_triop CT.Vnmls addr insn)
  | Bx -> append (convert_bx addr insn)
  | Bl -> append (convert_bl binf inforec addr insn)
  | B -> append (convert_branch binf inforec addr insn)
  | Conditional (cond, B) -> append (convert_cbranch cond addr insn)
  | Conditional (cond, _) ->
      convert_conditional binf inforec addr cond insn ilist blk_id bseq
			  bseq_cons
  | Shifted (opc, shift) ->
      convert_shift binf inforec addr insn ilist opc shift blk_id bseq bseq_cons
  | Rsc | Teq | Umaal | Mls | Umull | Umlal | Smull | Smlal | Bfc | Vmov_r2d_lo
  | Vmov_r2d_hi | Vmov_d2r_lo | Vmov_d2r_hi | Vmsr ->
      append (C.Nullary CT.Untranslated)
  | BAD -> append (C.Nullary CT.Untranslated)
  (*| x -> raise (Unsupported_opcode x) *)

and convert_conditional binf inforec addr cond insn ilist blk_id bseq bseq_cons =
  let cond_passed = create_blkref () in
  let after_insn = create_blkref () in
  let cond = C.Control (C.Branch (convert_condition cond, cond_passed,
				  after_insn)) in
  let ilist = CS.snoc ilist cond in
  let bseq' = finish_block blk_id ilist bseq bseq_cons in
  let cond_ilist, cond_blk_id, bseq'' =
    match insn.opcode with
      Conditional (_, op) ->
        convert_insn binf inforec addr { insn with opcode = op } CS.empty
		     cond_passed bseq' bseq_cons
    | _ -> failwith "not a conditional insn" in
  let cond_ilist' =
    if C.finishes_with_control cond_ilist then
      cond_ilist
    else
      CS.snoc cond_ilist (C.Control (C.Jump after_insn)) in
  let bseq'3 = finish_block cond_blk_id cond_ilist' bseq'' bseq_cons in
  CS.empty, after_insn, bseq'3

and convert_shift binf inforec addr insn ilist opc shift blk_id bseq bseq_cons =
  if insn.write_flags = [] && insn.read_flags == [] then begin
    let num_reads = Array.length insn.read_operands in
    let amount = convert_operand addr (insn.read_operands.(num_reads - 1))
    and operand = convert_operand addr (insn.read_operands.(num_reads - 2)) in
    let new_reads = Array.sub insn.read_operands 0 (num_reads - 1) in
    let num_reads' = Array.length new_reads in
    let shifted_operand = make_shifted_operand shift operand amount in
    new_reads.(num_reads' - 1) <- shifted_operand;
    convert_insn binf inforec addr { insn with opcode = opc;
      read_operands = new_reads } ilist blk_id bseq bseq_cons
  end else
    CS.snoc ilist (C.Nullary (CT.Untranslated)), blk_id, bseq


let convert_block binf inforec block_id bseq bseq_cons addr insn_list
		  code_hash =
  let frame_base = ref None in
  let code_deque, blk_id', bseq', last_offset = Deque.fold_left
    (fun (ilist, blk_id, bseq, offset) insn ->
      let insn_addr = Int32.add addr offset in
      let ilist', blk_id', bseq'
        = convert_insn binf inforec insn_addr insn ilist blk_id bseq
		       bseq_cons in
      ilist', blk_id', bseq', Int32.add offset 4l)
    (CS.empty, block_id, bseq, 0l)
    insn_list in
  let next_addr = Int32.add addr last_offset in
  if Hashtbl.mem code_hash next_addr then
    finish_block blk_id' ~chain:(BS.BlockAddr next_addr) code_deque
		 bseq' bseq_cons
  else begin
    if C.finishes_with_control code_deque then
      finish_block blk_id' code_deque bseq' bseq_cons
    else
      (* This is how we represent the end of a block of code which appears to
         fall through into nothingness (which is probably dead anyway).  *)
      let code_deque' = CS.snoc code_deque (C.Control C.Virtual_exit) in
      finish_block blk_id' code_deque' bseq' bseq_cons
  end

exception Out_of_range

exception Non_aggregate

(* Return aggr_member_id, type of member.  FIXME: We don't necessarily always
   want the innermost member.  If we know the type of the context (e.g. a
   function argument), we might be able to do better.  *)

let rec resolve_aggregate_access typ base_expr offset ctypes_for_cu =
  Log.printf 4 "resolve_aggregate_access, type %s, offset %d\n"
    (Ctype.string_of_ctype typ) offset;
  match typ with
    Ctype.C_struct (_, agmem)
  | Ctype.C_union (_, agmem) ->
      let found_mem =
        List.find
	  (fun mem ->
	    Log.printf 4
	      "checking member for %d: name %s, offset %d, size %d\n" offset
	      mem.Ctype.name mem.Ctype.offset mem.Ctype.size;
	    offset >= mem.Ctype.offset
		      && offset < mem.Ctype.offset + mem.Ctype.size)
	  agmem in
      if Ctype.base_type_p found_mem.Ctype.typ then
        C.Unary (CT.Aggr_member found_mem.Ctype.name, base_expr)
      else
        let sub =
	  resolve_aggregate_access found_mem.Ctype.typ base_expr
	    (offset - found_mem.Ctype.offset) ctypes_for_cu in
	C.Unary (CT.Aggr_member found_mem.Ctype.name, sub)
  | Ctype.C_pointer ptt -> base_expr
  | Ctype.C_array (arrsz, memtype) ->
      let memsize = Ctype.type_size ctypes_for_cu memtype in
      if offset mod memsize == 0 then
        let arr_offset = offset / memsize in
	C.Binary (CT.Array_element, base_expr,
		  C.Immed (Int32.of_int arr_offset))
      else
        failwith "offset not at multiple of array member size"
  | Ctype.C_typedef typename ->
      let targ = Hashtbl.find ctypes_for_cu.Ctype.ct_typedefs typename in
      resolve_aggregate_access targ base_expr offset ctypes_for_cu
  | Ctype.C_typetag typename ->
      let targ = Hashtbl.find ctypes_for_cu.Ctype.ct_typetags typename in
      resolve_aggregate_access targ base_expr offset ctypes_for_cu
  | _ ->
      Log.printf 2 "Unhandled type: %s\n" (Ctype.string_of_ctype typ);
      raise Non_aggregate
