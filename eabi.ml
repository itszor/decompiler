open Locations

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type arg_info =
  {
    mutable next_arg_reg : int;
    mutable stack_offset : int
  }

let in_hard_registers lo num =
  if num = 1 then
    In (C.Reg (CT.Hard_reg lo))
  else begin
    let parts = ref [] in
    for i = 0 to num - 1 do
      parts := ((i * 4), 4, In (C.Reg (CT.Hard_reg (lo + i)))) :: !parts
    done;
    Parts (List.rev !parts)
  end

let on_stack bytes_in_regs offset num_words =
  if num_words = 1 then
    In (C.Reg (CT.Stack offset))
  else begin
    let parts = ref [] in
    for i = 0 to num_words - 1 do
      parts := (bytes_in_regs + (i * 4), 4,
		In (C.Reg (CT.Stack (offset + i * 4)))) :: !parts
    done;
    Parts (List.rev !parts)
  end

let partly_in_registers lo offset num_words =
  let in_regs = 4 - lo in
  let in_mem = num_words - in_regs in
  let reg_part = in_hard_registers lo in_regs
  and mem_part = on_stack (4 * in_regs) offset in_mem in
  match reg_part, mem_part with
    In _, In _ -> Parts [(0, 4, reg_part); (4, 4, mem_part)]
  | In _, Parts px -> Parts ((0, 4, reg_part) :: px)
  | Parts px, In _ -> Parts (px @ [(4 * in_regs, 4, mem_part)])
  | Parts pr, Parts pm -> Parts (pr @ pm)
  | _ -> failwith "partly_in_registers"

let make_arg_accum () =
  {
    next_arg_reg = 0;
    stack_offset = 0
  }

let hidden_struct_return ft ct_for_cu =
  let rtype = ft.Function.return in
  let typesize = Ctype.type_size ct_for_cu rtype in
  typesize > 4 && Ctype.aggregate_type ct_for_cu rtype

let eabi_arg_loc ft argno arg_accum ct_for_cu =
  if argno = 0 && hidden_struct_return ft ct_for_cu then begin
    assert (arg_accum.next_arg_reg = 0);
    arg_accum.next_arg_reg <- 1
  end;
  let argtype = ft.Function.args.(argno) in
  let typesize = Ctype.type_size ct_for_cu argtype in
  let padded_size = (typesize + 3) land (lnot 3) in
  let alignment =
    if Ctype.aggregate_type ct_for_cu argtype then 4 else padded_size in
  let align_numregs = alignment / 4 in
  let regs_required = padded_size / 4 in
  let lo_reg = (arg_accum.next_arg_reg + align_numregs - 1)
	       land (lnot (align_numregs - 1)) in
  let aligned_offset = (arg_accum.stack_offset + alignment - 1)
		       land (lnot (alignment - 1)) in
  if lo_reg + regs_required <= 4 then begin
    (* Wholly in registers.  *)
    arg_accum.next_arg_reg <- lo_reg + regs_required;
    in_hard_registers lo_reg regs_required
  end else if arg_accum.next_arg_reg < 4 then begin
    (* Partly in registers.  *)
    assert (alignment == 4);
    arg_accum.stack_offset <- aligned_offset + 4 * (4 - arg_accum.next_arg_reg);
    arg_accum.next_arg_reg <- 4;
    partly_in_registers lo_reg aligned_offset regs_required
  end else begin
    (* Wholly on the stack.  *)
    arg_accum.stack_offset <- aligned_offset + padded_size;
    on_stack 0 aligned_offset regs_required
  end

let eabi_return_loc ft ct_for_cu =
  if hidden_struct_return ft ct_for_cu then
    (* This is kind of a weird representation.  At this point, we can probably
       do with just the size of the returned data: we need to add this to the
       stack map for the function, then resolve any accesses to the returned
       object.  *)
    Some (In (C.Binary (Irtypes.Aggr_return, C.Reg (CT.Hard_reg 0),
			C.Immed (Int32.of_int
				  (Ctype.type_size ct_for_cu
						   ft.Function.return)))))
  else begin
    match ft.Function.return with
      Ctype.C_void -> None
    | _ ->
      let tsize = Ctype.type_size ct_for_cu ft.Function.return in
      Some (in_hard_registers 0 ((tsize + 3) / 4))
  end
