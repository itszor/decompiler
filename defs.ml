module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type classification =
    Constant
  | Variable

type def_info = {
  src : C.code;
  mutable classification : classification;
  mutable ctype : Ctype.ctype option;
  mutable orig_name : string option
}

let get_defs blk_arr =
  let ht = Hashtbl.create 10 in
  Array.iter
    (fun blk ->
      CS.iter
        (function
	  C.Set (C.SSAReg (rd, rdn), src) ->
	    let classify =
	      match src with
		C.Immed imm -> Constant
	      | _ -> Variable in
	    let di = {
	      src = src;
	      classification = classify;
	      ctype = None;
	      orig_name = None
	    } in
	    Hashtbl.add ht (rd, rdn) di
	| _ -> ())
	blk.Block.code)
    blk_arr;
  ht
