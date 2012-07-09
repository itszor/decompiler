(* Convert decoded INSN format into IR code type.  *)

open Insn

module CS = Ir.IrCS
module CT = Ir.IrCT
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
  let blk = Irtypes.BlockNum !blk_num in
  incr blk_num;
  blk

let convert_operand addr op =
  match op with
    Hard_reg 15 -> C.Entity (CT.PC (Int32.add addr 8l))
  | Hard_reg r -> C.Reg (CT.Hard_reg r)
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
    C.Nullary (Irtypes.Untranslated)

let convert_binop addr opcode insn =
  let convert_operand = convert_operand addr in
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (dst, C.Binary (opcode, op1, op2))
  end else
    C.Nullary (Irtypes.Untranslated)

let convert_bic addr insn =
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let op2 = convert_operand addr insn.read_operands.(1) in
    let new_reads = Array.copy insn.read_operands in
    new_reads.(1) <- Converted (C.Unary (Irtypes.Not, op2));
    convert_binop addr Irtypes.And { insn with read_operands = new_reads }
  end else
    C.Nullary (Irtypes.Untranslated)

let convert_rsb addr insn =
  let convert_operand = convert_operand addr in
  if insn.write_flags = [] && insn.read_flags = [] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (dst, C.Binary (Irtypes.Sub, op2, op1))
  end else
    C.Nullary (Irtypes.Untranslated)

let convert_carry_in_op addr opcode insn =
  let convert_operand = convert_operand addr in
  if insn.write_flags = [] && insn.read_flags = [C] then begin
    let dst = convert_operand insn.write_operands.(0)
    and op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (dst, C.Trinary (opcode, op1, op2,
	   C.Reg (CT.Status Irtypes.Carry)))
  end else
    C.Nullary (Irtypes.Untranslated)

let make_shifted_operand shift operand amount =
  let op =
    match shift with
      Lsl ->
	C.Binary (Irtypes.Lsl, operand, amount)
    | Lsr ->
	C.Binary (Irtypes.Lsr, operand, amount)
    | Asr ->
	C.Binary (Irtypes.Asr, operand, amount)
    | Ror ->
	C.Binary (Irtypes.Ror, operand, amount)
    | Rrx ->
	C.Binary (Irtypes.Rrx, operand, amount) in
  Converted op

let convert_address addr ainf insn base index =
  match ainf.addr_mode with
    Base_plus_imm
  | Base_plus_reg -> C.Binary (Irtypes.Add, base, index)
  | Base_minus_reg -> C.Binary (Irtypes.Sub, base, index)
  | Base_plus_shifted_reg shift ->
      let num_reads = Array.length insn.read_operands in
      let shift_amt = convert_operand addr insn.read_operands.(num_reads - 1) in
      let shifted_index = make_shifted_operand shift index shift_amt in
      C.Binary (Irtypes.Add, base, convert_operand addr shifted_index)
  | Base_minus_shifted_reg shift ->
      let num_reads = Array.length insn.read_operands in
      let shift_amt = convert_operand addr insn.read_operands.(num_reads - 1) in
      let shifted_index = make_shifted_operand shift index shift_amt in
      C.Binary (Irtypes.Sub, base, convert_operand addr shifted_index)

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
    let addr' = C.Binary (Irtypes.Add, base_reg,
			  C.Immed (Int32.of_int !offset)) in
    let reg, loads_pc = convert_maybe_pc_operand insn.write_operands.(i) in
    let load = C.Set (reg, C.Load (Irtypes.Word, addr')) in
    ilist_r := CS.snoc !ilist_r load;
    if minf.increment then
      offset := !offset + 4
    else
      offset := !offset - 4;
    if loads_pc then
      jump_to_tmp := Some reg
  done;
  if minf.mm_writeback then begin
    let stored_regs = Array.length insn.write_operands - 1 in
    let offset = if minf.increment then stored_regs * 4 else -stored_regs * 4 in
    let writeback = C.Set (base_reg,
			   C.Binary (Irtypes.Add, base_reg,
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
    let addr' = C.Binary (Irtypes.Add, base_reg,
			  C.Immed (Int32.of_int !offset)) in
    let store = C.Store (Irtypes.Word, addr',
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
			   C.Binary (Irtypes.Add, base_reg,
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
      Ne -> Irtypes.Status_ne
    | Eq -> Irtypes.Status_eq
    | Lt -> Irtypes.Status_lt
    | Le -> Irtypes.Status_le
    | Gt -> Irtypes.Status_gt
    | Ge -> Irtypes.Status_ge
    | Mi -> Irtypes.Status_ltu
    | Pl -> Irtypes.Status_geu
    | Hi -> Irtypes.Status_gtu
    | Ls -> Irtypes.Status_leu
    | Cc -> Irtypes.Status_cc
    | Cs -> Irtypes.Status_cs
    | Vc -> Irtypes.Status_vc
    | Vs -> Irtypes.Status_vs in
  C.Unary (code, C.Reg (CT.Status Irtypes.CondFlags))

(* This is entirely wrong!  *)

let convert_cond_bx cond addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    Hard_reg r ->
      let falseblock = Int32.add addr 4l in
      C.Control (C.Branch (convert_condition cond,
			   Irtypes.BlockAddr falseblock,
			   Irtypes.BlockAddr falseblock))
  | _ -> failwith "unexpected bx operand"

let find_symbol symbols strtab addr =
  try
    let symbol = Symbols.find_symbol_by_addr symbols addr in
    let symname = Symbols.symbol_name symbol strtab in
    CT.Symbol (symname, symbol)
  with Not_found ->
    CT.Absolute addr

let fn_args inforec callee_addr ft_args arglocs =
  let args_from_ctype = Array.mapi
    (fun i typ ->
      match arglocs.(i) with
        Some loc ->
	  begin match Dwarfreader.loc_for_addr callee_addr loc with
	    `DW_OP_reg r ->
	      let reg = CT.Hard_reg r in
	      let id = C.create_id () in
	      Typedb.record_reg_info_for_id inforec reg id
	        (Typedb.Used_as_type ft_args.(i));
	      C.With_id (id, C.Reg reg)
	  | `DW_OP_fbreg o ->
	      let stackreg = CT.Stack o in
	      let id = C.create_id () in
	      Typedb.record_reg_info_for_id inforec stackreg id
		(Typedb.Used_as_type ft_args.(i));
	      C.With_id (id, C.Load (Irtypes.Word,
			       C.Binary (Irtypes.Add, C.Reg (CT.Hard_reg 13),
					 C.Immed (Int32.of_int o))))
	  | x -> failwith "fn_args/location"
	  end
      | None ->
          Log.printf 3
	    "Warning: no loc for argument, falling back to cheap hack";
	  begin match i with
            (0 | 1 | 2 | 3) as r -> C.Reg (CT.Hard_reg r)
	  | n -> C.Load (Irtypes.Word,
			 C.Binary (Irtypes.Add, C.Reg (CT.Hard_reg 13),
				   C.Immed (Int32.of_int ((n - 4) * 4))))
	  end)
    ft_args in
  C.Nary (Irtypes.Fnargs, Array.to_list args_from_ctype)

let add_incoming_args ft code =
  let (_, code') = Array.fold_left
    (fun (argn, code) arg ->
      match argn with
        (0 | 1 | 2 | 3) -> succ argn, code
      | n ->
          let arg_in = C.Store (Irtypes.Word,
	    C.Binary (Irtypes.Add, C.Reg (CT.Hard_reg 13),
		      C.Immed (Int32.of_int ((n - 4) * 4))),
	    C.Nullary Irtypes.Arg_in) in
	  succ argn, CS.snoc code arg_in)
    (0, code)
    ft.Function.args in
  code'

(* FT is a function_info record from function.ml.  INFOREC is an info record.
   CODESEQ is a code sequence for the virtual entry block for a function.  *)

let add_real_incoming_args ft start_addr inforec codeseq =
  let known_incoming_regs = ref [] in
  let _, added_args = Array.fold_left
    (fun (i, codeseq') typ ->
      match ft.Function.arg_locs.(i) with
        Some loc ->
	  begin match Dwarfreader.loc_for_addr start_addr loc with
	    `DW_OP_reg r ->
	      let reg = CT.Hard_reg r in
	      let id = C.create_id () in
	      known_incoming_regs := r :: !known_incoming_regs;
	      Typedb.record_reg_info_for_id inforec reg id
	        (Typedb.Type_known typ);
	      let insn = C.Set (C.With_id (id, C.Reg reg),
				C.Nullary Irtypes.Arg_in) in
	      succ i, CS.snoc codeseq' insn
	  | `DW_OP_fbreg o ->
	      let stackreg = CT.Stack o in
	      let id = C.create_id () in
	      Typedb.record_reg_info_for_id inforec stackreg id
	        (Typedb.Type_known typ);
	      let insn = C.With_id (id, C.Store (Irtypes.Word,
			   C.Binary (Irtypes.Add, C.Reg (CT.Hard_reg 13),
				     C.Immed (Int32.of_int o)),
			   C.Nullary Irtypes.Arg_in)) in
	      succ i, CS.snoc codeseq' insn
	  | _ -> failwith "add_real_incoming_args/location"
	  end
      | None -> failwith "no loc for incoming arg")
    (0, codeseq)
    ft.Function.args in
  List.fold_left
    (fun codeseq' regnum ->
      if List.mem regnum !known_incoming_regs then
        codeseq'
      else
        CS.snoc codeseq' (C.Set (C.Reg (CT.Hard_reg regnum),
				 C.Nullary Irtypes.Arg_in)))
    added_args
    [0; 1; 2; 3]

let fn_ret = function
    Ctype.C_void -> C.Nullary Irtypes.Nop
  | _ -> C.Set (C.Reg (CT.Hard_reg 0), C.Entity CT.Arg_out)

exception Calling of string

(* This is awful: a circular dependency!  Find a nicer solution...  *)
let symbol_for_plt_entry = ref (fun _ _ -> failwith "binding")

let convert_bl binf inforec addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let no_arg = C.Nullary Irtypes.Nop in
      let ret_addr = Irtypes.BlockAddr (Int32.add addr 4l) in
      let call_addr = Int32.add addr i in
      let targ_sec = Elfreader.get_section_num_by_addr binf.Binary_info.elfbits
		       binf.Binary_info.ehdr binf.Binary_info.shdr_arr
		       call_addr in
      let targ_sec_name = Elfreader.get_section_name binf.Binary_info.elfbits
			    binf.Binary_info.ehdr binf.Binary_info.shdr_arr
			    targ_sec in
      begin match targ_sec_name with
        ".text" ->
	  let cu_for_dest = Binary_info.cu_offset_for_address binf call_addr in
	  let cu_inf = Hashtbl.find binf.Binary_info.cu_hash cu_for_dest in
	  let sym = Hashtbl.find cu_inf.Binary_info.ci_symtab call_addr
	  and die = Hashtbl.find cu_inf.Binary_info.ci_dieaddr call_addr in
	  let symname = Symbols.symbol_name sym binf.Binary_info.strtab in
	  (*let sym_or_addr = find_symbol binf.Binary_info.symbols
					binf.Binary_info.strtab call_addr in*)
	  let fn_inf =
	    Function.function_type binf.Binary_info.debug_loc symname die
	      cu_inf.Binary_info.ci_dietab cu_inf.Binary_info.ci_ctypes
	      ~compunit_baseaddr:cu_inf.Binary_info.ci_baseaddr in
	  let ct_sym = CT.Finf_sym (symname, fn_inf, sym) in
	  let passes = fn_args inforec call_addr fn_inf.Function.args
			       fn_inf.Function.arg_locs
	  and returns = fn_ret fn_inf.Function.return in
	  C.Control (C.Call_ext (CT.EABI, ct_sym, passes, ret_addr, returns))
      | ".plt" ->
          let sym, sym_name =
	    try
	      let sym = (!symbol_for_plt_entry) binf call_addr in
	      let sym_name = Symbols.symbol_name sym binf.Binary_info.dynstr in
	      sym, sym_name
	    with Not_found ->
	      List.hd binf.Binary_info.symbols,
	      Printf.sprintf "<plt@%lx>" call_addr in
	  begin try
	    let fn_inf = Builtin.builtin_function_type sym_name in
            C.Control (C.Call_ext (CT.Plt_call, CT.Symbol (sym_name, sym),
				   fn_args inforec call_addr
				     fn_inf.Function.args
				     fn_inf.Function.arg_locs, ret_addr,
				   fn_ret fn_inf.Function.return))
	  with Not_found ->
            C.Control (C.Call_ext (CT.Plt_call, CT.Symbol (sym_name, sym),
				   no_arg, ret_addr, no_arg))
	  end
      | x -> raise (Calling x)
      end
  | _ -> failwith "unexpected bx operand"

let convert_cmp addr insn =
  let convert_operand = convert_operand addr in
  if insn.read_flags = [] && flags_match insn.write_flags [C;V;N;Z] then begin
    let op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (C.Reg (CT.Status Irtypes.CondFlags),
	   C.Binary (Irtypes.Cmp, op1, op2))
  end else
    C.Nullary (Irtypes.Untranslated)

let convert_tst addr insn =
  let convert_operand = convert_operand addr in
  if insn.read_flags = [] && flags_match insn.write_flags [N;Z] then begin
    let op1 = convert_operand insn.read_operands.(0)
    and op2 = convert_operand insn.read_operands.(1) in
    C.Set (C.Reg (CT.Status Irtypes.CondFlags),
	   C.Binary (Irtypes.Tst, op1, op2))
  end else
    C.Nullary (Irtypes.Untranslated)

let convert_cbranch cond addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let trueblock = Irtypes.BlockAddr (Int32.add addr i)
      and falseblock = Irtypes.BlockAddr (Int32.add addr 4l) in
      C.Control (C.Branch (convert_condition cond, trueblock, falseblock))
  | _ -> failwith "unexpected b<cond> operand"

let convert_branch addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      C.Control (C.Jump (Irtypes.BlockAddr (Int32.add addr i)))
  | _ -> failwith "unexpected b operand"

exception Unsupported_opcode of Insn.opcode

let name_for_block_id = function
    Irtypes.BlockAddr addr -> Printf.sprintf "block_for_addr_0x%lx" addr
  | Irtypes.BlockNum n -> Printf.sprintf "block_num_%d" n
  | Irtypes.Virtual_entry -> "virtual_entry"
  | Irtypes.Virtual_exit -> "virtual_exit"

(* Start a new block, adding the insns for the previous block to the block
   sequence and adding it to the block index hashtbl.  If the insn list
   doesn't end with a control flow insn and CHAIN is set to a block id, adds a
   jump from the end of the old block to the new one.  Returns new blockseq.  *)

let finish_block block_id ?chain insnlist bseq bseq_cons =
  let insnlist' =
    if not (CS.is_empty insnlist) then begin
      match CS.noced insnlist with
	prev, C.Control _ -> insnlist
      | _ ->
        begin match chain with
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
  let name = name_for_block_id block_id in
  let blk = Block.make_block name insnlist' in
  bseq_cons block_id blk bseq

let rec convert_insn binf inforec addr insn ilist blk_id bseq bseq_cons =
  let ilist = CS.snoc ilist (C.Entity (CT.Insn_address addr)) in
  let append insn =
    CS.snoc ilist insn, blk_id, bseq
  and same_blk ilist =
    ilist, blk_id, bseq in
  match insn.opcode with
    Mov -> append (convert_mov addr insn)
  | Add -> append (convert_binop addr Irtypes.Add insn)
  | Sub -> append (convert_binop addr Irtypes.Sub insn)
  | And -> append (convert_binop addr Irtypes.And insn)
  | Eor -> append (convert_binop addr Irtypes.Eor insn)
  | Orr -> append (convert_binop addr Irtypes.Or insn)
  | Bic -> append (convert_bic addr insn)
  | Mul -> append (convert_binop addr Irtypes.Mul insn)
  | Rsb -> append (convert_rsb addr insn)
  | Adc -> append (convert_carry_in_op addr Irtypes.Adc insn)
  | Sbc -> append (convert_carry_in_op addr Irtypes.Sbc insn)
  | Cmp -> append (convert_cmp addr insn)
  | Tst -> append (convert_tst addr insn)
  | Ldr ainf -> same_blk (convert_load addr ainf insn Irtypes.Word ilist)
  | Ldrb ainf -> same_blk (convert_load addr ainf insn Irtypes.U8 ilist)
  | Str ainf -> same_blk (convert_store addr ainf insn Irtypes.Word ilist)
  | Strb ainf -> same_blk (convert_store addr ainf insn Irtypes.U8 ilist)
  | Ldrh ainf -> same_blk (convert_load addr ainf insn Irtypes.U16 ilist)
  | Strh ainf -> same_blk (convert_store addr ainf insn Irtypes.U16 ilist)
  | Ldrsh ainf -> same_blk (convert_load addr ainf insn Irtypes.S16 ilist)
  | Ldrsb ainf -> same_blk (convert_load addr ainf insn Irtypes.S8 ilist)
  | Strd ainf -> same_blk (convert_store addr ainf insn Irtypes.Dword ilist)
  | Ldrd ainf -> same_blk (convert_load addr ainf insn Irtypes.Dword ilist)
  | Ldm minf -> same_blk (convert_ldm addr minf insn ilist)
  | Stm minf -> same_blk (convert_stm addr minf insn ilist)
  | Bx -> append (convert_bx addr insn)
  | Bl -> append (convert_bl binf inforec addr insn)
  | B -> append (convert_branch addr insn)
  | Conditional (cond, B) -> append (convert_cbranch cond addr insn)
  | Conditional (cond, _) ->
      convert_conditional binf inforec addr cond insn ilist blk_id bseq
			  bseq_cons
  | Shifted (opc, shift) ->
      convert_shift binf inforec addr insn ilist opc shift blk_id bseq bseq_cons
  | x -> raise (Unsupported_opcode x)

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
  let cond_ilist' = CS.snoc cond_ilist (C.Control (C.Jump after_insn)) in
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
    CS.snoc ilist (C.Nullary (Irtypes.Untranslated)), blk_id, bseq


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
    finish_block blk_id' ~chain:(Irtypes.BlockAddr next_addr) code_deque
		 bseq' bseq_cons
  else
    finish_block blk_id' code_deque bseq' bseq_cons

exception Out_of_range

let base_type_p = function
    Ctype.C_struct _
  | Ctype.C_union _
  | Ctype.C_array _ -> false
  | _ -> true

exception Non_aggregate

(* Return aggr_member_id, type of member.  FIXME: We don't necessarily always
   want the innermost member.  If we know the type of the context (e.g. a
   function argument), we might be able to do better.  *)

let rec resolve_aggregate_access typ offset ctypes_for_cu =
  Log.printf 4 "resolve_aggregate_access, type %s, offset %d\n"
    (Ctype.string_of_ctype typ) offset;
  match typ with
    Ctype.C_struct agmem
  | Ctype.C_union agmem ->
      let found_mem =
        List.find
	  (fun mem ->
	    Log.printf 4
	      "checking member for %d: name %s, offset %d, size %d\n" offset
	      mem.Ctype.name mem.Ctype.offset mem.Ctype.size;
	    offset >= mem.Ctype.offset
		      && offset < mem.Ctype.offset + mem.Ctype.size)
	  agmem in
      if base_type_p found_mem.Ctype.typ then
        Irtypes.Aggr_leaf found_mem.Ctype.name, found_mem.Ctype.typ
      else
        let sub, inner_type =
	  resolve_aggregate_access found_mem.Ctype.typ
	    (offset - found_mem.Ctype.offset) ctypes_for_cu in
	Irtypes.Aggr_sub (found_mem.Ctype.name, sub), inner_type
  | Ctype.C_typedef typename ->
      let targ = Hashtbl.find ctypes_for_cu.Ctype.ct_typedefs typename in
      resolve_aggregate_access targ offset ctypes_for_cu
  | _ ->
      raise Non_aggregate
