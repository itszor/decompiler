open Elfreader
open Binary_info

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let decode_stub binf addr =
  (* We're not interested in gathering info for stubs.  *)
  let inforec = Typedb.create_info () in
  let plt_sec_num = get_section_number binf.elfbits binf.ehdr binf.shdr_arr
				       ".plt" in
  let plt_start_addr = binf.shdr_arr.(plt_sec_num).sh_addr in
  let stub_offset = Int32.sub addr plt_start_addr in
  let stub_bits = Bitstring.dropbits (8 * (Int32.to_int stub_offset))
				     binf.plt in
  let stub_insns = ref Deque.empty in
  for i = 0 to 2 do
    let decoded =
      Decode_arm.decode_insn (Bitstring.dropbits (i * 32) stub_bits) in
    stub_insns := Deque.snoc !stub_insns decoded
  done;
  Insn_to_ir.convert_block binf inforec (Irtypes.BlockAddr addr) BS.empty
			   (fun _ blk bseq -> BS.cons blk bseq) addr
			   !stub_insns (Hashtbl.create 0)

(* A decoded PLT stub looks like this:

     r12 := add (pc(0x2ec0), 0)
     r12 := add (r12, 339968)
     tmp1 := load-word[add (r12, -1676)]
     r12 := add (r12, -1676)
     --> compjump_ext (branch_exchange, tmp1)
   
   Decode this by just evaluating r12, and ignoring the load of the PC and
   subsequent compjump_ext.  *)

let evaluate_insn r12_val = function
    C.Set (C.Reg (CT.Hard_reg 12), C.Binary (Irtypes.Add,
					     C.Entity (CT.PC pc_val),
					     C.Immed imm)) ->
      Int32.add pc_val imm
  | C.Set (C.Reg (CT.Hard_reg 12), C.Binary (Irtypes.Add,
					     C.Reg (CT.Hard_reg 12),
					     C.Immed imm)) ->
      Int32.add r12_val imm
  | C.Set (_, C.Load _) -> r12_val
  | C.Control _ -> r12_val
  | C.Entity _ -> r12_val
  | _ -> failwith "Unexpected insn in PLT stub"

let evaluate_stub stub_bs =
  let stub_block = (BS.head stub_bs).Block.code in
  CS.fold_left evaluate_insn 0l stub_block

let find_reloc binf addr =
  match Array.fold_left
    (fun found rel ->
      match found with
        Some f -> Some f
      | None -> if rel.rel_offset = addr then Some rel else None)
    None
    binf.parsed_rel_plt with
    Some f -> f
  | None -> raise Not_found

let symbol_for_reloc binf reloc =
  List.nth binf.dyn_symbols reloc.rel_sym_index

(* See name with e.g.:

   let sym = Plt.symbol_for_plt_entry binf 0x2f6cl in
   Symbols.symbol_name sym binf.dynstr
*)

let symbol_for_plt_entry binf addr =
  let r12_val = evaluate_stub (decode_stub binf addr) in
  let reloc = find_reloc binf r12_val in
  symbol_for_reloc binf reloc

(* Hack around circular dependency.  *)
let _ =
  Insn_to_ir.symbol_for_plt_entry := symbol_for_plt_entry
