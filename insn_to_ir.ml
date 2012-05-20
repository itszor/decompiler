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

let convert_address ainf insn base index =
  match ainf.addr_mode with
    Base_plus_imm
  | Base_plus_reg -> C.Binary (Irtypes.Add, base, index)
  | Base_minus_reg -> C.Binary (Irtypes.Sub, base, index)

let convert_load addr ainf insn access ilist =
  let convert_operand = convert_operand addr in
  let base = convert_operand insn.read_operands.(0)
  and index = convert_operand insn.read_operands.(1) in
  let addr = convert_address ainf insn base index
  and dst, loads_pc = convert_maybe_pc_operand insn.write_operands.(0) in
  let ilist' = if ainf.pre_modify then begin
    let ilist = CS.snoc ilist (C.Set (dst, C.Load (access, addr))) in
    if ainf.writeback then
      let w_base = convert_operand insn.write_operands.(1) in
      CS.snoc ilist (C.Set (w_base, addr))
    else
      ilist
  end else begin
    assert ainf.writeback;
    let w_base = convert_operand insn.write_operands.(1) in
    let ilist = CS.snoc ilist (C.Set (dst, C.Load (access, base))) in
    CS.snoc ilist (C.Set (w_base, addr))
  end in
  if loads_pc then
    CS.snoc ilist' (C.Control (C.CompJump_ext (CT.Branch_exchange, dst)))
  else
    ilist'

let convert_store addr ainf insn access ilist =
  let convert_operand = convert_operand addr in
  let base = convert_operand insn.read_operands.(1)
  and index = convert_operand insn.read_operands.(2) in
  let addr = convert_address ainf insn base index
  and src = convert_operand insn.read_operands.(0) in
  if ainf.pre_modify then begin
    let ilist = CS.snoc ilist (C.Store (access, addr, src)) in
    if ainf.writeback then
      let w_base = convert_operand insn.write_operands.(0) in
      CS.snoc ilist (C.Set (w_base, addr))
    else
      ilist
  end else begin
    assert ainf.writeback;
    let w_base = convert_operand insn.write_operands.(0) in
    let ilist = CS.snoc ilist (C.Store (access, base, src)) in
    CS.snoc ilist (C.Set (w_base, addr))
  end

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

let fn_args ft_args =
  let args_from_ctype = Array.mapi
    (fun i typ ->
      match i with
        (0 | 1 | 2 | 3) as r -> C.Reg (CT.Hard_reg r)
      | n -> C.Load (Irtypes.Word,
		     C.Binary (Irtypes.Add, C.Reg (CT.Hard_reg 13),
			       C.Immed (Int32.of_int ((n - 4) * 4)))))
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

let fn_ret = function
    Ctype.C_void -> C.Nullary Irtypes.Nop
  | _ -> C.Set (C.Reg (CT.Hard_reg 0), C.Entity CT.Arg_out)

let convert_bl binf addr insn =
  let dest = insn.read_operands.(0) in
  match dest with
    PC_relative i ->
      let no_arg = C.Nullary Irtypes.Nop in
      let ret_addr = Irtypes.BlockAddr (Int32.add addr 4l) in
      let call_addr = Int32.add addr i in
      let cu_for_dest = Binary_info.cu_offset_for_address binf call_addr in
      let cu_inf = Hashtbl.find binf.Binary_info.cu_hash cu_for_dest in
      let sym = Hashtbl.find cu_inf.Binary_info.ci_symtab call_addr
      and die = Hashtbl.find cu_inf.Binary_info.ci_dieaddr call_addr in
      let symname = Symbols.symbol_name sym binf.Binary_info.strtab in
      let ct_sym = CT.Symbol (symname, sym) in
      (*let sym_or_addr = find_symbol binf.Binary_info.symbols
				    binf.Binary_info.strtab call_addr in*)
      let fn_inf = Function.function_type symname die
					  cu_inf.Binary_info.ci_dietab in
      let abi, passes, returns =
	CT.EABI, fn_args fn_inf.Function.args, fn_ret fn_inf.Function.return in
      C.Control (C.Call_ext (abi, ct_sym, passes, ret_addr, returns))
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
	None -> insnlist
      | Some chain ->
	  let fallthru = C.Control (C.Jump chain) in
	  CS.snoc insnlist fallthru
    end in
  let name = name_for_block_id block_id in
  let blk = Block.make_block name insnlist' in
  bseq_cons block_id blk bseq

let rec convert_insn binf addr insn ilist blk_id bseq bseq_cons =
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
  | Mul -> append (convert_binop addr Irtypes.Mul insn)
  | Rsb -> append (convert_rsb addr insn)
  | Adc -> append (convert_carry_in_op addr Irtypes.Adc insn)
  | Sbc -> append (convert_carry_in_op addr Irtypes.Sbc insn)
  | Cmp -> append (convert_cmp addr insn)
  | Ldr ainf -> same_blk (convert_load addr ainf insn Irtypes.Word ilist)
  | Ldrb ainf -> same_blk (convert_load addr ainf insn Irtypes.U8 ilist)
  | Str ainf -> same_blk (convert_store addr ainf insn Irtypes.Word ilist)
  | Strb ainf -> same_blk (convert_store addr ainf insn Irtypes.U8 ilist)
  | Bx -> append (convert_bx addr insn)
  | Bl -> append (convert_bl binf addr insn)
  | B -> append (convert_branch addr insn)
  | Conditional (cond, B) -> append (convert_cbranch cond addr insn)
  | Conditional (cond, _) ->
      convert_conditional binf addr cond insn ilist blk_id bseq bseq_cons
  | x -> raise (Unsupported_opcode x)

and convert_conditional binf addr cond insn ilist blk_id bseq bseq_cons =
  let cond_passed = create_blkref () in
  let after_insn = create_blkref () in
  let cond = C.Control (C.Branch (convert_condition cond, cond_passed,
				  after_insn)) in
  let ilist = CS.snoc ilist cond in
  let bseq' = finish_block blk_id ilist bseq bseq_cons in
  let cond_ilist, cond_blk_id, bseq'' =
    match insn.opcode with
      Conditional (_, op) ->
        convert_insn binf addr { insn with opcode = op } CS.empty cond_passed
		     bseq' bseq_cons
    | _ -> failwith "not a conditional insn" in
  let cond_ilist' = CS.snoc cond_ilist (C.Control (C.Jump after_insn)) in
  let bseq'3 = finish_block cond_blk_id cond_ilist' bseq'' bseq_cons in
  CS.empty, after_insn, bseq'3

let convert_block binf block_id bseq bseq_cons addr insn_list code_hash =
  let code_deque, blk_id', bseq', last_offset = Deque.fold_left
    (fun (acc, blk_id, bseq, offset) insn ->
      let ilist', blk_id', bseq'
        = convert_insn binf (Int32.add addr offset) insn acc blk_id bseq
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
