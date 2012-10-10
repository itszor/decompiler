module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

let find_args blk_arr virtual_entry =
  let ht = Hashtbl.create 10 in
  let blk = blk_arr.(virtual_entry).Block.code in
  CS.iter
    (function
      C.Set (C.SSAReg regid, C.Nullary (Irtypes.Arg_in num)) ->
        Hashtbl.add ht regid num
    | _ -> ())
    blk;
  ht

let substitute_args blk_arr ht finf vars =
  Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt ->
	  C.map
	    (function
	      C.Set (C.SSAReg _, C.Nullary (Irtypes.Arg_in _)) as foo ->
	        C.Protect foo
	    | C.SSAReg regid when Hashtbl.mem ht regid ->
	        let argno = Hashtbl.find ht regid in
		if argno < Array.length finf.Function.arg_names then begin
		  let name = finf.Function.arg_names.(argno) in
		  let r = CT.Stack_var name in
		  Hashtbl.add vars (Vartypes.T_reg r)
		    { Vartypes.vt_name = name;
		      vt_type = finf.Function.args.(argno);
		      vt_needs_prototype = false };
		  C.Reg r
		end else
		  C.SSAReg regid
	    | x -> x)
	    stmt)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr
