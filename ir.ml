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
    type extop = unit
    type reg = Hard_reg of int
             | Stack of int
	     | Temp of int
	     | Status of ir_statusbits
	     | Arg_out
	     | Caller_restored
    type mem = ir_mem
    type entity = PC of int32
		| Symbol_addr of string * Elfreader.elf_sym
    type abi = Branch_exchange
	     | Unknown_abi

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

    let string_of_binop = function
      Add -> "add"
    | Sub -> "sub"
    | And -> "and"
    | Eor -> "eor"
    | Or -> "or"
    | Mul -> "mul"
    | Cmp -> "cmp"
    
    let string_of_triop = function
      Adc -> "adc"
    | Sbc -> "sbc"
    
    let string_of_extop = fun _ -> ""

    let string_of_status = function
      Carry -> "carry"
    | CondFlags -> "condflags"
    | NZFlags -> "nzflags"

    let string_of_reg = function
      Hard_reg r -> Printf.sprintf "r%d" r
    | Stack s -> Printf.sprintf "stack+%d" s
    | Temp t -> Printf.sprintf "tmp%d" t
    | Status sb -> Printf.sprintf "status(%s)" (string_of_status sb)
    | Arg_out -> "arg_out"
    | Caller_restored -> "caller_restored"
    
    let string_of_mem = function
      U8 -> "u8"
    | S8 -> "s8"
    | U16 -> "u16"
    | S16 -> "s16"
    | Word -> "word"
    
    let string_of_entity = function
      PC loc -> Printf.sprintf "pc(0x%lx)" loc
    | Symbol_addr (name, _) -> Printf.sprintf "&%s" name

    let string_of_abi = function
      Branch_exchange -> "branch_exchange"
    | Unknown_abi -> "unknown_abi"
    
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
