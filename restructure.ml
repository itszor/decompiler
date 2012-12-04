open Locations

module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type nesting =
    Anon_block of scope_contents
(*| For_loop of block_contents
  | Do_loop of block_contents
  | While_loop of block_contents
  | If_stmt of block_contents
  | If_else_stmt of block_contents * block_contents
  | Switch_stmt of block_contents*)

and block_or_nested =
    Block_ref of int
  | Nested of nesting

and scope_contents =
  {
    mutable locals : local_var list;
    bbs_in_scope : block_or_nested list;
  }

and local_var =
  {
    var_name : string;
    var_type : Ctype.ctype;
    var_initialiser : C.code option;
    var_origin : origin;
    var_location : location list
  }

and origin =
    Incoming_arg
  | Local


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

let eabi_arg_loc ft argno arg_accum ct_for_cu =
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

let convert_args ft ct_for_cu =
  let locals = ref [] in
  let accum = make_arg_accum () in
  for i = 0 to Array.length ft.Function.args - 1 do
    let name = ft.Function.arg_names.(i)
    and typ = ft.Function.args.(i)
    and loc_opt = ft.Function.arg_locs.(i) in
    match loc_opt with
      None -> failwith "need a location for an argument"
    | Some loc ->
        let local = {
	  var_name = name;
	  var_type = typ;
	  var_initialiser = None;
	  var_origin = Incoming_arg;
	  var_location = [eabi_arg_loc ft i accum ct_for_cu]
	} in
	Log.printf 3 "arg %s, loc %s\n" local.var_name
	  (String.concat " && "
	    (List.map string_of_location local.var_location));
	locals := local :: !locals
  done;
  !locals

let restructure blk_arr ft ct_for_cu =
  let bbs_in_func = ref [] in
  for idx = Array.length blk_arr - 1 downto 0 do
    match blk_arr.(idx).Block.id with
      Irtypes.Virtual_entry | Irtypes.Virtual_exit -> ()
    | _ -> bbs_in_func := Block_ref idx :: !bbs_in_func
  done;
  let arg_locals = convert_args ft ct_for_cu in
  Anon_block { locals = arg_locals; bbs_in_scope = !bbs_in_func }
