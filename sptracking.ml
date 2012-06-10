(* Attempt to resolve stack accesses.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let string_of_offset_option = function
    None -> "unknown"
  | Some x -> string_of_int x

let print_sp_offsets blk =
  Log.printf 3 "block id '%s': start sp offset %s, end sp offset %s\n"
    blk.Block.id (string_of_offset_option blk.Block.start_sp_offset)
    (string_of_offset_option blk.Block.end_sp_offset)

let set_or_ensure_equal blk part old_offset_opt new_offset =
  match old_offset_opt with
    Some old_offset when old_offset = new_offset -> old_offset_opt
  | None -> Some new_offset
  | Some old_offset ->
      Log.printf 3 "SP offset differs at %s of '%s': %d vs %d\n"
        part blk.Block.id old_offset new_offset;
      old_offset_opt

let sp_reg = function
    C.SSAReg (CT.Hard_reg 13, _) -> true
  | C.Reg (CT.Hard_reg 13) -> true
  | _ -> false

let offset_from_current_sp loc =
  match loc with
    `DW_OP_reg 13 -> 0
  | `DW_OP_breg (13, offs) -> Big_int.int_of_big_int offs
  | _ -> failwith "offset_from_current_sp"

(* We can sometimes tell the names and proper types of registers too -- that's
   not handled at present, and probably won't be handled here anyway.  *)

let fb_relative_var_loc loc =
  match loc with
    Dwarfreader.Loc_expr (`DW_OP_fbreg offs) -> offs
  | _ -> raise Not_found

let known_var vars sp_offset =
  let fv, ofs =
    List.fold_left
      (fun ((found_var, offset) as prev) var ->
	match var.Function.var_location with
          None -> prev
	| Some loc ->
            try
	      let var_offset = fb_relative_var_loc loc in
	      if sp_offset >= var_offset
		 && sp_offset < (var_offset + var.Function.var_size) then begin
		Log.printf 3 "sp offset:%d var_offset:%d var_size:%d\n"
		  sp_offset var_offset var.Function.var_size;
		Some var, sp_offset - var_offset
	      end else
		prev
	    with Not_found -> prev)
      (None, 0)
      vars in
  match fv with
    Some f -> f, ofs
  | None -> raise Not_found

module IrPhiPlacement = Phi.PhiPlacement (Ir.IrCT) (Ir.IrCS) (Ir.IrBS)

let try_rewrite_var vars offset stack_vars insn rewrite_as ctypes_for_cu =
  try
    let kvar, var_ofs = known_var vars offset in
    Log.printf 3 "Offset %d looks like variable %s (+%d)\n"
      offset kvar.Function.var_name var_ofs;
    let sv = CT.Stack_var kvar.Function.var_name in
    stack_vars := IrPhiPlacement.R.add sv !stack_vars;
    let aggr_access, _ =
      Insn_to_ir.resolve_aggregate_access kvar.Function.var_type var_ofs
					  ctypes_for_cu in
    (*let blk = {
      Irtypes.ctype = kvar.Function.var_type;
      block_size = kvar.Function.var_size;
      access_size = Irtypes.Word
    } in*)
    match rewrite_as with
      `load dst ->
	C.Protect (C.Set (dst,
		     C.Load (Irtypes.Word,
		       C.Unary (Irtypes.Aggr_member (kvar.Function.var_type,
		        			     aggr_access),
			 C.Unary (Irtypes.Address_of, C.Reg sv)))))
    | `store src ->
        C.Protect (C.Store (Irtypes.Word,
		     C.Unary (Irtypes.Aggr_member (kvar.Function.var_type,
						   aggr_access),
		       C.Unary (Irtypes.Address_of, C.Reg sv)),
		     src))
    | `ssa_reg ->
        C.Protect (C.Unary (Irtypes.Aggr_member (kvar.Function.var_type,
						 aggr_access),
		     C.Unary (Irtypes.Address_of, C.Reg sv)))
  with Not_found ->
    insn

exception Sp_tracking_failed

let sp_track blk_arr vars ctypes_for_cu =
  let spht = Hashtbl.create 10
  and framebase_loc = ref None
  and stack_vars = ref IrPhiPlacement.R.empty in
  let sp_derived = function
    C.SSAReg (r, rn) -> Hashtbl.mem spht (r, rn)
  | _ -> false in
  let sp_used code =
    C.fold
      (fun expr found ->
        match expr with
	  C.Load (m, addr) as e -> C.Protect e, found
	| C.Set (dst, src) -> C.Set (C.Protect dst, src), found
	| x when sp_reg x || sp_derived x -> x, true
	| x -> x, found)
      code
      false in
  let derived_offset base offset =
    if sp_reg base then
      offset
    else
      match base with
	C.SSAReg (r, rn) -> Hashtbl.find spht (r, rn)
      | _ -> raise Not_found in
  let derive_sp offset = function
    (* Copy stack pointer to another register.  *)
    C.Set (C.SSAReg (r, rn), src) when sp_reg src ->
      Hashtbl.add spht (r, rn) offset
    (* Copy stack pointer to another register, with +/- offset.  *)
  | C.Set (C.SSAReg (r, rn) as dst, C.Binary (Irtypes.Add, base, C.Immed imm))
      when sp_reg base ->
      Log.printf 3 "adding offset %d for %s\n" (offset + Int32.to_int imm)
        (C.string_of_code dst);
      Hashtbl.add spht (r, rn) (offset + Int32.to_int imm)
  | C.Set (C.SSAReg (r, rn), C.Binary (Irtypes.Sub, base, C.Immed imm))
      when sp_reg base ->
      Hashtbl.add spht (r, rn) (offset - Int32.to_int imm)
    (* Copy register derived from stack pointer to another register, with an
       additional offset.  *)
  | C.Set (C.SSAReg (r, rn), C.Binary (Irtypes.Add, base, C.Immed imm))
      when sp_derived base ->
      let offset' = derived_offset base offset in
      Hashtbl.add spht (r, rn) (offset' + Int32.to_int imm)
  | C.Set (C.SSAReg (r, rn), C.Binary (Irtypes.Sub, base, C.Immed imm))
      when sp_derived base ->
      let offset' = derived_offset base offset in
      Hashtbl.add spht (r, rn) (offset' - Int32.to_int imm)
    (* ...or without additional offset.  *)
  | C.Set (C.SSAReg (r, rn), base) when sp_derived base ->
      let offset' = derived_offset base offset in
      Hashtbl.add spht (r, rn) offset'
  | x ->
      Log.printf 3 "Don't know how to derive SP from '%s'\n"
	(C.string_of_code x);
      raise Sp_tracking_failed in
  let underive_sp insn r rn offset =
    Log.printf 3 "Copying sp-derived var back to SP in '%s'\n"
      (C.string_of_code insn);
    let offset' = try
      Hashtbl.find spht (r, rn)
    with Not_found ->
      Log.printf 3 "Unknown sp-derived reg\n";
      offset in
    Log.printf 3 "Offset now %d\n" offset';
    offset' in
  let rewrite_sp_from_dwarf_frame insn offset framebase_loc_opt =
    (* Try to find a variable in the stack frame which we might be trying
       to access.  This won't always work because the Dwarf info doesn't tend
       to be complete.  *)
      (*begin match framebase_loc_opt with
        Some framebase_loc ->
	  let fb_offset = offset_from_current_sp framebase_loc in
	  Log.printf 3
	    "Frame base offset according to Dwarf info: %d, tracking says %d\n"
	    fb_offset (-offset)
      | None ->
          Log.printf 3
	    "Dwarf info says nothing about frame base here, tracking says %d\n"
	    (-offset)
      end;*)
      C.map
        (fun x -> match x with
          (* Loads.  *)
	  C.Set (dst, C.Load (Irtypes.Word,
			      C.Binary (Irtypes.Add, base, C.Immed imm)))
	    when sp_reg base || sp_derived base ->
	    let offset' = derived_offset base offset in
	    let real_stack_offset = offset' + Int32.to_int imm in
	    try_rewrite_var vars real_stack_offset stack_vars x (`load dst)
			    ctypes_for_cu
	| C.Set (dst, C.Load (Irtypes.Word,
			      C.Binary (Irtypes.Sub, base, C.Immed imm)))
	    when sp_reg base || sp_derived base ->
	    let offset' = derived_offset base offset in
	    let real_stack_offset = offset' - Int32.to_int imm in
            try_rewrite_var vars real_stack_offset stack_vars x (`load dst)
			    ctypes_for_cu
	| C.Set (dst, C.Load (Irtypes.Word, base))
	    when sp_reg base || sp_derived base ->
	    let offset' = derived_offset base offset in
	    try_rewrite_var vars offset' stack_vars x (`load dst) ctypes_for_cu
	  (* Stores.  *)
	 | C.Store (Irtypes.Word, C.Binary (Irtypes.Add, base, C.Immed imm),
		    src) when sp_reg base || sp_derived base ->
	     let offset' = derived_offset base offset in
	     let real_stack_offset = offset' + Int32.to_int imm in
	     try_rewrite_var vars real_stack_offset stack_vars x (`store src)
			     ctypes_for_cu
	 | C.Store (Irtypes.Word, C.Binary (Irtypes.Sub, base, C.Immed imm),
		    src) when sp_reg base || sp_derived base ->
	     let offset' = derived_offset base offset in
	     let real_stack_offset = offset' - Int32.to_int imm in
	     try_rewrite_var vars real_stack_offset stack_vars x (`store src)
			     ctypes_for_cu
	 | C.Store (Irtypes.Word, base, src)
	     when sp_reg base || sp_derived base ->
	     let offset' = derived_offset base offset in
	     try_rewrite_var vars offset' stack_vars x (`store src)
			     ctypes_for_cu
	  (* Other.  *)
	| C.SSAReg _ when sp_derived x ->
	    let offset' = derived_offset x offset in
	    try_rewrite_var vars offset' stack_vars x `ssa_reg ctypes_for_cu
	| x -> x)
	insn in
  let rewrite_sp insn offset =
    C.map
      (function
        (* Loads.  *)
	C.Set (dst, C.Load (Irtypes.Word,
			    C.Binary (Irtypes.Add, base, C.Immed imm)))
	  when sp_reg base || sp_derived base ->
	  let offset' = derived_offset base offset in
	  C.Protect (C.Set (dst, C.Reg (CT.Stack (offset' + Int32.to_int imm))))
      | C.Set (dst, C.Load (Irtypes.Word,
			    C.Binary (Irtypes.Sub, base, C.Immed imm)))
	  when sp_reg base || sp_derived base ->
	  let offset' = derived_offset base offset in
          C.Protect (C.Set (dst, C.Reg (CT.Stack (offset' - Int32.to_int imm))))
      | C.Set (dst, C.Load (Irtypes.Word, base))
	  when sp_reg base || sp_derived base ->
	  let offset' = derived_offset base offset in
	  C.Protect (C.Set (dst, C.Reg (CT.Stack offset')))
	(* Stores.  *)
      | C.Store (Irtypes.Word, C.Binary (Irtypes.Add, base, C.Immed imm), src)
	  when sp_reg base || sp_derived base ->
	  let offset' = derived_offset base offset in
	  C.Protect (C.Set (C.Reg (CT.Stack (offset' + Int32.to_int imm)), src))
      | C.Store (Irtypes.Word, C.Binary (Irtypes.Sub, base, C.Immed imm), src)
	  when sp_reg base || sp_derived base ->
	  let offset' = derived_offset base offset in
	  C.Protect (C.Set (C.Reg (CT.Stack (offset' - Int32.to_int imm)), src))
      | C.Store (Irtypes.Word, base, src) when sp_reg base || sp_derived base ->
	  let offset' = derived_offset base offset in
	  C.Protect (C.Set (C.Reg (CT.Stack offset'), src))
	(* Function arguments, etc.  *)
      | C.Load (Irtypes.Word, C.Binary (Irtypes.Add, base, C.Immed imm))
          when sp_reg base || sp_derived base ->
	  let offset' = derived_offset base offset in
	  (* This is used for function arguments.  *)
	  C.Protect (C.Reg (CT.Stack (offset' + Int32.to_int imm)))
      | C.SSAReg _ as x when sp_derived x ->
          let offset' = derived_offset x offset in
          C.Protect (C.Unary (Irtypes.Address_of, C.Reg (CT.Stack offset')))
      | x -> x)
      insn in
  Block.clear_visited blk_arr;
  let rec scan blk sp_offset =
    blk.Block.start_sp_offset
      <- set_or_ensure_equal blk "start" blk.Block.start_sp_offset sp_offset;
    let code', sp_offset' = CS.fold_left
      (fun (code, off) insn ->
        match insn with
	  C.Entity (CT.Frame_base_update loc) ->
	    framebase_loc := Some loc;
	    code, off
	  (* Add/subtract the real stack pointer. *)
	| C.Set (dst, C.Binary (Irtypes.Add, src, C.Immed imm))
	    when sp_reg dst && sp_reg src ->
	    code, off + (Int32.to_int imm)
	| C.Set (dst, C.Binary (Irtypes.Sub, src, C.Immed imm))
	    when sp_reg dst && sp_reg src ->
	    code, off - (Int32.to_int imm)
	| C.Set (dst, C.Nullary Irtypes.Special) ->
	    (* Ignore this pseudo-insn.  *)
	    CS.snoc code insn, off
	  (* Copy another register to the stack pointer.  *)
	| C.Set (dst, C.SSAReg (r, rn)) when sp_reg dst ->
	    code, underive_sp insn r rn off
	| C.Set (dst, C.Binary (Irtypes.Add, C.SSAReg (r, rn), C.Immed i))
	    when sp_reg dst ->
	    code, underive_sp insn r rn (off + Int32.to_int i)
	| C.Set (dst, C.Binary (Irtypes.Sub, C.SSAReg (r, rn), C.Immed i))
	    when sp_reg dst ->
	    code, underive_sp insn r rn (off - Int32.to_int i)
	  (* Copy something else to the stack pointer.  *)
	| C.Set (dst, _) when sp_reg dst ->
	    Log.printf 3 "Unexpected write to sp in '%s'\n"
	      (C.string_of_code insn);
	    CS.snoc code insn, off
	  (* Copy value derived from the stack pointer to a different
	     register.  *)
	| C.Set (dst, src) when sp_used src ->
	    Log.printf 3
	      "SP derived var '%s' in '%s' (initial sp offset %d)\n"
	      (C.string_of_code dst) (C.string_of_code insn) off;
	    derive_sp off insn;
	    code, off
	  (* Other uses of the stack pointer, or stack-pointer-derived
	     registers.  *)
	| _ ->
	  let insn' = rewrite_sp_from_dwarf_frame insn off !framebase_loc in
	  CS.snoc code (rewrite_sp insn' off), off)
      (CS.empty, sp_offset)
      blk.Block.code in
    blk.Block.code <- code';
    blk.Block.end_sp_offset
      <- set_or_ensure_equal blk "end" blk.Block.end_sp_offset sp_offset';
    print_sp_offsets blk;
    blk.Block.visited <- true;
    List.iter
      (fun nextblk_ref ->
        let nextblk = blk_arr.(nextblk_ref) in
        if not nextblk.Block.visited then
	  scan nextblk sp_offset')
      blk.Block.idomchild in
  scan blk_arr.(0) 0;
  !stack_vars
