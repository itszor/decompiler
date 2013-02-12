open Elfreader
open Binary_info

module BS = Ir.IrBS
module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

exception Unrecognized_tablejump

(* This is really a hack: jump tables always look the same.  The comparison
   always immediately precedes the jump.  We could be more general with more
   sophisticated analysis, but we need to resolve tablejumps quite early in
   decompilation, when lots of helpful metadata isn't available.  *)

let decode_tablejump binf secbits sym addr =
  let inforec = Typedb.create_info () in
  let tablejump_start = Int32.sub addr 4l in
  let offset = Int32.sub tablejump_start binf.shdr_arr.(sym.st_shndx).sh_addr in
  let text_bits = offset_section secbits offset in
  let jump_insns = ref CS.empty in
  for i = 0 to 1 do
    let decoded =
      Decode_arm.decode_insn (Bitstring.dropbits (i * 32) text_bits) in
    jump_insns := CS.snoc !jump_insns decoded
  done;
  match CS.to_list !jump_insns with
    [{ Insn.opcode = Insn.Cmp;
       read_operands = [| Insn.Hard_reg reg; Insn.Immediate hi_bound |] };
     { Insn.opcode = Insn.Conditional (Insn.Ls,
				       Insn.Shifted (Insn.Add, Insn.Lsl));
       read_operands = [| Insn.Hard_reg 15; Insn.Hard_reg jump_reg;
			  Insn.Immediate 2l |];
       write_operands = [| Insn.Hard_reg 15 |] }] when reg = jump_reg ->
      Log.printf 3 "Found jump table at 0x%lx\n" addr;
      Log.printf 3 "Hi bound: %ld\n" hi_bound;
      Log.printf 3 "Index register: %d\n" jump_reg;
      hi_bound, jump_reg
  | _ -> raise Unrecognized_tablejump

let blocklist_for_jumptable blockseq ht addr num =
  let blkrefs = ref [] in
  for i = num - 1 downto 0 do
    let addr' = Int32.add addr (Int32.of_int (i * 4)) in
    let addr_ref = Irtypes.BlockAddr addr' in
    if not (Hashtbl.mem ht addr_ref) then
      raise Unrecognized_tablejump;
    blkrefs := addr_ref :: !blkrefs
  done;
  !blkrefs

let repair_jumptables binf secbits blockseq ht sym =
  let blockseq' = BS.map
    (fun blk ->
      let insn_addr = ref None in
      let codeseq' = CS.fold_left
        (fun codeseq stmt ->
	  match stmt with
	    C.Entity (CT.Insn_address addr) ->
	      insn_addr := Some addr;
	      CS.snoc codeseq stmt
	  | C.Control (C.CompJump (code, [])) ->
	      begin match !insn_addr with
		None ->
		  Log.printf 3
		    "Ignoring possible tablejump, address unknown\n";
		  CS.snoc codeseq stmt
	      | Some addr ->
		  Log.printf 3 "Possible jump table at 0x%lx\n" addr;
		  begin try
		    let hi_bound, idx_reg =
		      decode_tablejump binf secbits sym addr in
		    let blocklist =
		      blocklist_for_jumptable blockseq ht (Int32.add addr 8l)
					      (Int32.to_int hi_bound + 1) in
		    begin match CS.noced codeseq with
		      Some (drop_last, _) ->
			CS.snoc drop_last (C.Control (C.CompJump
					   (C.Reg (CT.Hard_reg idx_reg),
						   blocklist)))
		    | None -> failwith "?"
		    end
		  with Unrecognized_tablejump ->
		    Log.printf 3
		      "Unrecognized tablejump at 0x%lx\n" addr;
		    CS.snoc codeseq stmt
		  end
	      end
	  | _ -> CS.snoc codeseq stmt)
	CS.empty
	blk.Block.code in
      { blk with Block.code = codeseq' })
    blockseq in
  blockseq'
