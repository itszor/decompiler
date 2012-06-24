module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type classification =
    Constant
  | Variable

type def_info = {
  src : C.code;
  mutable num_uses : int;
  mutable classification : classification;
  mutable ctype : Ctype.ctype option;
  mutable orig_name : string option
}

let count_uses blk_arr defs =
  Array.iter
    (fun blk ->
      CS.iter
        (fun stmt ->
	  ignore (C.map
	    (fun node ->
	      match node with
		C.Set (dst, src) -> C.Set (C.Protect dst, src)
	      | C.SSAReg (rs, rsn) ->
	          let dinf = Hashtbl.find defs (rs, rsn) in
		  dinf.num_uses <- dinf.num_uses + 1;
		  node
	      | _ -> node)
	    stmt))
	blk.Block.code)
    blk_arr

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
	      orig_name = None;
	      num_uses = 0
	    } in
	    Hashtbl.add ht (rd, rdn) di
	| _ -> ())
	blk.Block.code)
    blk_arr;
  count_uses blk_arr ht;
  ht
