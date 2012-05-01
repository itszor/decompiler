(* Attempt to resolve stack accesses.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let string_of_offset_option = function
    None -> "unknown"
  | Some x -> string_of_int x

let print_sp_offsets blk =
  Printf.printf "block id '%s': start sp offset %s, end sp offset %s\n"
    blk.Block.id (string_of_offset_option blk.Block.start_sp_offset)
    (string_of_offset_option blk.Block.end_sp_offset)

let set_or_ensure_equal blk part old_offset_opt new_offset =
  match old_offset_opt with
    Some old_offset when old_offset = new_offset -> old_offset_opt
  | None -> Some new_offset
  | Some old_offset ->
      Printf.printf "SP offset differs at %s of '%s': %d vs %d\n"
        part blk.Block.id old_offset new_offset;
      old_offset_opt

let sp_track blk_arr =
  let spht = Hashtbl.create 10 in
  let sp_reg = function
      C.SSAReg (CT.Hard_reg 13, _) -> true
    | C.Reg (CT.Hard_reg 13) -> true
    | _ -> false in
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
  let derive_sp offset = function
    C.Set (C.SSAReg (r, rn), src) when sp_reg src ->
      Hashtbl.add spht (r, rn) offset
  | C.Set (C.SSAReg (r, rn), C.Binary (Irtypes.Add, base, C.Immed imm))
      when sp_reg base ->
      Hashtbl.add spht (r, rn) (offset + Int32.to_int imm)
  | C.Set (C.SSAReg (r, rn), C.Binary (Irtypes.Sub, base, C.Immed imm))
      when sp_reg base ->
      Hashtbl.add spht (r, rn) (offset - Int32.to_int imm)
  | x -> Printf.printf "Don't know how to derive SP from '%s'\n"
	   (C.string_of_code x) in
  let underive_sp insn r rn offset =
    Printf.printf "Copying sp-derived var back to SP in '%s'\n"
      (C.string_of_code insn);
    let offset' = try
      Hashtbl.find spht (r, rn)
    with Not_found ->
      Printf.printf "Unknown sp-derived reg\n";
      offset in
    Printf.printf "Offset now %d\n" offset';
    offset' in
  Array.iter (fun blk -> blk.Block.visited <- false) blk_arr;
  let rec scan blk sp_offset =
    blk.Block.start_sp_offset
      <- set_or_ensure_equal blk "start" blk.Block.start_sp_offset sp_offset;
    let sp_offset' = CS.fold_left
      (fun off insn ->
        match insn with
	  C.Set (dst, C.Binary (Irtypes.Add, src, C.Immed imm))
	    when sp_reg dst && sp_reg src ->
	    off + (Int32.to_int imm)
	| C.Set (dst, C.Binary (Irtypes.Sub, src, C.Immed imm))
	    when sp_reg dst && sp_reg src ->
	    off - (Int32.to_int imm)
	| C.Set (dst, C.Nullary Irtypes.Special) ->
	    (* Ignore this pseudo-insn.  *)
	    off
	| C.Set (dst, C.SSAReg (r, rn)) when sp_reg dst ->
	    underive_sp insn r rn off
	| C.Set (dst, C.Binary (Irtypes.Add, C.SSAReg (r, rn), C.Immed i))
	    when sp_reg dst ->
	    underive_sp insn r rn (off + Int32.to_int i)
	| C.Set (dst, C.Binary (Irtypes.Sub, C.SSAReg (r, rn), C.Immed i))
	    when sp_reg dst ->
	    underive_sp insn r rn (off - Int32.to_int i)
	| C.Set (dst, _) when sp_reg dst ->
	    Printf.printf "Unexpected write to sp in '%s'\n"
	      (C.string_of_code insn);
	    off
	| C.Set (dst, src) when sp_used src ->
	    Printf.printf
	      "SP derived var '%s' in '%s' (initial sp offset %d)\n"
	      (C.string_of_code dst) (C.string_of_code insn) off;
	    derive_sp off insn;
	    off
	| _ -> off)
      sp_offset
      blk.Block.code in
    blk.Block.end_sp_offset
      <- set_or_ensure_equal blk "end" blk.Block.end_sp_offset sp_offset';
    print_sp_offsets blk;
    blk.Block.visited <- true;
    List.iter
      (fun successor ->
        if not successor.Block.visited then scan successor sp_offset')
      blk.Block.successors in
  scan blk_arr.(0) 0
