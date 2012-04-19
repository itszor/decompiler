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
	     | Carry
    type mem = ir_mem
    type entity = unit
    type abi = Branch_exchange
	     | Unknown_abi

    type blockref = int
    type immed = int32
    type addr = Absolute of int32
              | Reg_addr of int
	      | Symbol of Elfreader.elf_sym
    
    let string_of_nulop = fun _ -> ""
    let string_of_unop = fun _ -> ""
    let string_of_binop = fun _ -> ""
    let string_of_triop = fun _ -> ""
    let string_of_extop = fun _ -> ""
    let string_of_reg = fun _ -> ""
    let string_of_mem = fun _ -> ""
    let string_of_entity = fun _ -> ""
    let string_of_abi = fun _ -> ""
    let string_of_immed = fun _ -> ""
    let string_of_addr = fun _ -> ""
  end

module IrBS =
  struct
    include Ranlist
    type blockref = int32
    type reftable = (int32, int) Hashtbl.t
    
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
    
    let string_of_blockref x = Int32.to_string x
  end

module IrCS =
  struct
    include Deque
    
    let get_last = tp
  end

module Ir = Code.Code (IrCT) (IrCS) (IrBS)
