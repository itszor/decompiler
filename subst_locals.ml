module BS = Ir.IrBS
module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let subst_locals blk_arr ft ctypes_for_cu =
  let defs = Defs.get_defs blk_arr in
  Array.map
    (fun blk ->
      let newseq = CS.fold_left
        (fun newseq stmt ->
	  let stmt' = C.map
	    (function
	      C.Set (dst, src) -> C.Set (C.Protect dst, src)
	    | (C.SSAReg id) as ssareg ->
	        let def = Hashtbl.find defs id in
		begin match def.Defs.src with
		  C.Entity (CT.Arg_var x) as var -> var
		| C.Ternary (CT.Var_slice, (C.Entity (CT.Arg_var x) as argvar),
			     C.Immed lo, C.Immed sz) ->
		    let typ = Function.arg_type_by_name ft x in
		    Insn_to_ir.resolve_aggregate_access typ argvar
		      (Int32.to_int lo) ctypes_for_cu
		| _ -> ssareg
		end
	    | x -> x)
	    stmt in
	  CS.snoc newseq stmt')
	CS.empty
	blk.Block.code in
      { blk with Block.code = newseq })
    blk_arr
