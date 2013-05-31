(* Track dynamic stack updates over the basic blocks of a function.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let string_of_offset_option = function
    None -> "unknown"
  | Some x -> string_of_int x

let print_sp_offsets blk =
  Log.printf 3 "block id '%s': start sp offset %s, end sp offset %s\n"
    (BS.string_of_blockref blk.Block.id)
    (string_of_offset_option blk.Block.start_sp_offset)
    (string_of_offset_option blk.Block.end_sp_offset)

let set_or_ensure_equal blk part old_offset_opt new_offset =
  match old_offset_opt with
    Some old_offset when old_offset = new_offset -> old_offset_opt
  | None -> Some new_offset
  | Some old_offset ->
      Log.printf 3 "SP offset differs at %s of '%s': %d vs %d\n"
        part (BS.string_of_blockref blk.Block.id) old_offset new_offset;
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

(*module IrPhiPlacement = Phi.PhiPlacement (Ir.IrCT) (Ir.IrCS) (Ir.IrBS)*)

exception Sp_tracking_failed

let sp_track blk_arr =
  let spht = Hashtbl.create 10
  and cov = Coverage.create_coverage 0l 0xffffffffl in
  
  let sp_derived = function
    C.SSAReg (r, rn) -> Hashtbl.mem spht (r, rn)
  | _ -> false in

  let rec sp_used code =
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
  | C.Set (C.SSAReg (r, rn) as dst, C.Binary (CT.Add, base, C.Immed imm))
      when sp_reg base ->
      Log.printf 3 "adding offset %d for %s\n" (offset + Int32.to_int imm)
        (C.string_of_code dst);
      Hashtbl.add spht (r, rn) (offset + Int32.to_int imm)
  | C.Set (C.SSAReg (r, rn), C.Binary (CT.Sub, base, C.Immed imm))
      when sp_reg base ->
      Hashtbl.add spht (r, rn) (offset - Int32.to_int imm)
    (* Copy register derived from stack pointer to another register, with an
       additional offset.  *)
  | C.Set (C.SSAReg (r, rn), C.Binary (CT.Add, base, C.Immed imm))
      when sp_derived base ->
      let offset' = derived_offset base offset in
      Hashtbl.add spht (r, rn) (offset' + Int32.to_int imm)
  | C.Set (C.SSAReg (r, rn), C.Binary (CT.Sub, base, C.Immed imm))
      when sp_derived base ->
      let offset' = derived_offset base offset in
      Hashtbl.add spht (r, rn) (offset' - Int32.to_int imm)
    (* ...or without additional offset.  *)
  | C.Set (C.SSAReg (r, rn), base) when sp_derived base ->
      let offset' = derived_offset base offset in
      Hashtbl.add spht (r, rn) offset'
  | C.Set (C.Entity CT.Arg_out, _) ->
      ()
    (* Maybe we can handle Phi nodes here -- if all the inputs correspond to
       the same thing.  Dunno how likely that is.  *)
  | x ->
      Log.printf 3 "Don't know how to derive SP from '%s'\n"
	(C.string_of_code x);
      () in

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

  Block.clear_visited blk_arr;

  let rec scan blk sp_offset =
    blk.Block.start_sp_offset
      <- set_or_ensure_equal blk "start" blk.Block.start_sp_offset sp_offset;
    let sp_offset' = CS.fold_left
      (fun off insn ->
        match insn with
	  C.Entity (CT.Insn_address ia) ->
	    Coverage.add_range cov (Coverage.Half_open (off, ia));
	    off
	  (* Add/subtract the real stack pointer. *)
	| C.Set (dst, C.Binary (CT.Add, src, C.Immed imm))
	    when sp_reg dst && sp_reg src ->
	    off + (Int32.to_int imm)
	| C.Set (dst, C.Binary (CT.Sub, src, C.Immed imm))
	    when sp_reg dst && sp_reg src ->
	    off - (Int32.to_int imm)
	| C.Set (dst, C.Nullary CT.Special) ->
	    (* Ignore this pseudo-insn.  *)
	    off
	  (* Copy another register to the stack pointer.  *)
	| C.Set (dst, C.SSAReg (r, rn)) when sp_reg dst ->
	    underive_sp insn r rn off
	| C.Set (dst, C.Binary (CT.Add, C.SSAReg (r, rn), C.Immed i))
	    when sp_reg dst ->
	    underive_sp insn r rn (off + Int32.to_int i)
	| C.Set (dst, C.Binary (CT.Sub, C.SSAReg (r, rn), C.Immed i))
	    when sp_reg dst ->
	    underive_sp insn r rn (off - Int32.to_int i)
	  (* Ignore set from incoming SP...  *)
	| C.Set (_, C.Nullary CT.Incoming_sp) -> off
	  (* Copy something else to the stack pointer.  *)
	| C.Set (dst, _) when sp_reg dst ->
	    Log.printf 3 "Unexpected write to sp in '%s'\n"
	      (C.string_of_code insn);
	    off
	  (* Copy value derived from the stack pointer to a different
	     register.  *)
	| C.Set (dst, src) when sp_used src ->
	    Log.printf 3
	      "SP derived var '%s' in '%s' (initial sp offset %d)\n"
	      (C.string_of_code dst) (C.string_of_code insn) off;
	    derive_sp off insn;
	    off
	  (* Other uses of the stack pointer, or stack-pointer-derived
	     registers.  *)
	| _ ->
	    off)
      sp_offset
      blk.Block.code in
    blk.Block.end_sp_offset
      <- set_or_ensure_equal blk "end" blk.Block.end_sp_offset sp_offset';
    print_sp_offsets blk;
    blk.Block.visited <- true;
    List.iter
      (fun nextblk ->
        if not nextblk.Block.visited then
	  scan nextblk sp_offset')
      blk.Block.successors in

  (* Pass 1: Walk over code by DFS successors.  *)
  scan blk_arr.(0) 0;

  (* Pass 2: Attempt to resolve phi nodes.  FIXME: this doesn't do anything
     yet!  It may or may not be sufficient to detect if a function does dynamic
     stack allocation in a loop.  *)
  Array.iter
    (fun blk ->
      let code' = CS.fold_right
        (fun stmt codeseq ->
	  match stmt with
	    C.Set (dst, C.Phi phi_args) ->
	      Log.printf 3 "Attempt to resolve %s\n" (C.string_of_code stmt);
	      Array.iteri
	        (fun i arg ->
		  if sp_derived arg then
		    Log.printf 3 "Phi arg %d: %s, offset %d\n" i
		      (C.string_of_code arg) (derived_offset arg 0))
	        phi_args;
	      CS.cons stmt codeseq
	  | x -> CS.cons x codeseq)
	blk.Block.code
	CS.empty in
      blk.Block.code <- code')
    blk_arr;

  (* Return the coverage information.  *)
  cov
