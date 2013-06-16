(* Evaluate constant expressions -- or try to.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let create_metadata blk_arr =
  Defs.get_defs blk_arr

exception Non_constant

(* Evaluate const EXPR, returning int32.  *)

let rec eval_const ?pc_rel_load meta expr =
  match expr with
    C.Immed i -> i
  | C.SSAReg id ->
      begin try
        let dinf = Hashtbl.find meta id in
	eval_const ?pc_rel_load meta dinf.Defs.src
      with Not_found ->
        raise Non_constant
      end
  | C.Entity (CT.PC loc) -> loc
  | C.Binary (CT.Add, op1, op2) ->
      Int32.add (eval_const ?pc_rel_load meta op1)
		(eval_const ?pc_rel_load meta op2)
  | C.Binary (CT.Sub, op1, op2) ->
      Int32.sub (eval_const ?pc_rel_load meta op1)
		(eval_const ?pc_rel_load meta op2)
  | C.Binary (CT.And, op1, op2) ->
      Int32.logand (eval_const ?pc_rel_load meta op1)
		   (eval_const ?pc_rel_load meta op2)
  | C.Binary (CT.Or, op1, op2) ->
      Int32.logor (eval_const ?pc_rel_load meta op1)
		  (eval_const ?pc_rel_load meta op2)
  | C.Binary (CT.Eor, op1, op2) ->
      Int32.logxor (eval_const ?pc_rel_load meta op1)
		   (eval_const ?pc_rel_load meta op2)
  | C.Binary (CT.Lsl, op1, op2) ->
      Int32.shift_left (eval_const ?pc_rel_load meta op1)
		       (Int32.to_int (eval_const ?pc_rel_load meta op2))
  | C.Binary (CT.Lsr, op1, op2) ->
      Int32.shift_right_logical (eval_const ?pc_rel_load meta op1)
				(Int32.to_int
				  (eval_const ?pc_rel_load meta op2))
  | C.Binary (CT.Asr, op1, op2) ->
      Int32.shift_right (eval_const ?pc_rel_load meta op1)
			(Int32.to_int (eval_const ?pc_rel_load meta op2))
  | C.Unary (CT.Not, op1) ->
      Int32.lognot (eval_const ?pc_rel_load meta op1)
  | C.Load (_, C.Binary (CT.Add, C.Entity (CT.PC _), _)) ->
	begin match pc_rel_load with
	  Some prl -> prl meta expr
	| None -> raise Non_constant
        end
  | _ ->
      Log.printf 3 "Expr '%s' is not (recognized as) constant\n"
        (C.string_of_code expr);
      raise Non_constant
