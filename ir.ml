open Irtypes

(* An intermediate representation, in the form required by the generified
   "code" modules.  *)

(* Define types representing code.  *)
module IrCT =
  struct
    type nulop = ir_nulop
    type unop = ir_unop
    type binop = ir_binop
    type triop = ir_triop
    type extop = ir_extop
    type reg = Hard_reg of int
             | Stack of int
	     | Temp of int
	     | Status of ir_statusbits
	     | Stack_var of string
    type mem = ir_mem
    type entity = PC of int32
		| Symbol_addr of string * Elfreader.elf_sym
		| Section of string
		| Arg_out
		| Caller_restored
		| Frame_base_update of Dwarfreader.dwarf_op
		| String_constant of string
    type abi = Branch_exchange
	     | Unknown_abi
	     | Plt_call
	     | EABI

    type blockref = int
    type immed = int32
    type addr = Absolute of int32
	      | Symbol of string * Elfreader.elf_sym
    
    let string_of_nulop = function
      Nop -> "nop"
    | Untranslated -> "**UNTRANSLATED**"
    | Arg_in -> "arg_in"
    | Caller_saved -> "caller_saved"
    | Special -> "special"
    | Declaration ct -> Printf.sprintf "declaration(%s)"
	(Ctype.string_of_ctype ct)
    
    let rec string_of_member_id = function
      Aggr_leaf x -> x
    | Aggr_sub (x, subid) -> x ^ "." ^ (string_of_member_id subid)
    
    let string_of_unop = function
      Not -> "not"
    | Status_eq -> "status_eq"
    | Status_ne -> "status_ne"
    | Status_lt -> "status_lt"
    | Status_le -> "status_le"
    | Status_gt -> "status_gt"
    | Status_ge -> "status_ge"
    | Status_ltu -> "status_ltu"
    | Status_leu -> "status_leu"
    | Status_gtu -> "status_gtu"
    | Status_geu -> "status_geu"
    | Status_cc -> "status_cc"
    | Status_cs -> "status_cs"
    | Status_vc -> "status_vc"
    | Status_vs -> "status_vs"
    | Address_of -> "address_of"
    | Sxth -> "sxth"
    | Uxth -> "uxth"
    | Sxtb -> "sxtb"
    | Uxtb -> "uxtb"
    | Aggr_member (typ, agr) ->
	Printf.sprintf "aggregate_member.%s (%s)" (string_of_member_id agr)
	  (Ctype.string_of_ctype typ)

    let string_of_binop = function
      Add -> "add"
    | Sub -> "sub"
    | And -> "and"
    | Eor -> "eor"
    | Or -> "or"
    | Mul -> "mul"
    | Cmp -> "cmp"
    | Tst -> "tst"
    | Lsl -> "lsl"
    | Lsr -> "lsr"
    | Asr -> "asr"
    | Ror -> "ror"
    | Rrx -> "rrx"

    let string_of_triop = function
      Adc -> "adc"
    | Sbc -> "sbc"
    
    let string_of_extop = function
      Fnargs -> "fnargs"

    let string_of_status = function
      Carry -> "carry"
    | CondFlags -> "condflags"
    | NZFlags -> "nzflags"

    let string_of_reg = function
      Hard_reg r -> Printf.sprintf "r%d" r
    | Stack s -> Printf.sprintf "stack%s%d" (if s < 0 then "" else "+") s
    | Temp t -> Printf.sprintf "tmp%d" t
    | Status sb -> Printf.sprintf "status(%s)" (string_of_status sb)
    | Stack_var nm -> nm
    
    let rec string_of_mem = function
      U8 -> "u8"
    | S8 -> "s8"
    | U16 -> "u16"
    | S16 -> "s16"
    | Word -> "word"
    | Dword -> "dword"
    (*| Block blk ->
        Printf.sprintf "block(%d,%s)" blk.block_size
		       (string_of_mem blk.access_size)*)
    
    let string_of_entity = function
      PC loc -> Printf.sprintf "pc(0x%lx)" loc
    | Symbol_addr (name, _) -> Printf.sprintf "&%s" name
    | Section name -> Printf.sprintf "section(%s)" name
    | Arg_out -> "arg_out"
    | Caller_restored -> "caller_restored"
    | Frame_base_update _ -> "frame_base_update"
    | String_constant str ->
        Printf.sprintf "string_const(\"%s\")" (String.escaped str)

    let string_of_abi = function
      Branch_exchange -> "branch_exchange"
    | Unknown_abi -> "unknown_abi"
    | Plt_call -> "plt_call"
    | EABI -> "eabi"
    
    let string_of_immed i = Int32.to_string i

    let string_of_addr = function
      Absolute i -> Printf.sprintf "absolute(%lx)" i
    | Symbol (name, _) -> Printf.sprintf "symbol(%s)" name
  end

module IrBS =
  struct
    include Ranlist
    type blockref = ir_blockref
    type reftable = (ir_blockref, int) Hashtbl.t
    
    let of_index reftable x =
      let found = Hashtbl.fold
        (fun blkref idx acc ->
	  if x = idx then
	    Some blkref
	  else
	    acc)
	reftable
	None in
      match found with
        Some x -> x
      | None -> raise Not_found

    let to_index reftable x = Hashtbl.find reftable x
    
    let lookup_ref things reftable r = lookup things (to_index reftable r)
    
    let string_of_blockref = function
      BlockAddr x -> Printf.sprintf "addr_0x%lx" x
    | BlockNum i -> Printf.sprintf "block_num_%d" i
    | Virtual_entry -> "virtual_entry"
    | Virtual_exit -> "virtual_exit"
  end

module IrCS =
  struct
    include Deque
    
    let get_last = tp
  end

module Ir = Code.Code (IrCT) (IrCS) (IrBS)
