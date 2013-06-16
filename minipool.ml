(* Attempt to resolve minipool loads.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let minipool_resolve elfbits ehdr shdr_arr symbols mapping_syms strtab
		     blk_arr inforec ctypes_for_cu =
  let meta = Const.create_metadata blk_arr in
  let rec eval_minipool_const meta expr =
    match expr with
      C.Load (CT.Word, C.Binary (CT.Add, C.Entity (CT.PC loc), const_exp)) ->
	Log.printf 3 "pc relative load: '%s'\n" (C.string_of_code expr);
	let imm =
	  Const.eval_const ~pc_rel_load:eval_minipool_const meta const_exp in
	let addr = Int32.add loc imm in
	let mapping = Mapping.mapping_for_addr mapping_syms strtab addr in
	Log.printf 3 "mapping for addr 0x%lx is %s\n" addr
	  (Mapping.string_of_mapping mapping);
	let section_num =
	  Elfreader.get_section_num_by_addr elfbits ehdr shdr_arr addr in
	let section_name =
	  Elfreader.get_section_name elfbits ehdr shdr_arr section_num in
	Log.printf 3 "address is in section %s " section_name;
	let writable =
	  Elfreader.section_writable shdr_arr.(section_num) in
	if writable then begin
	  Log.printf 3 "(writable)\n";
	  raise Const.Non_constant
	end else
	  Log.printf 3 "(read-only)\n";
	let section = Elfreader.extract_section elfbits
			shdr_arr.(section_num) in
	let word =
	  Elfreader.get_word shdr_arr.(section_num) section addr in
	Log.printf 3 "loads word: %lx\n" word;
	word
    | _ -> Const.eval_const ~pc_rel_load:eval_minipool_const meta expr in
  Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt ->
	  match stmt with
	    C.Set (C.SSAReg id,
		   (C.Load (CT.Word,
		     C.Binary (CT.Add, C.Entity (CT.PC loc),
			       const_exp)) as rhs)) ->
	      begin try
	        let new_rhs = eval_minipool_const meta rhs in
		Log.printf 3 "Replacing minipool load with constant %lx\n"
		  new_rhs;
		C.Set (C.SSAReg id, C.Immed new_rhs)
	      with Const.Non_constant ->
	        Log.printf 3 "Didn't form constant for minipool load (%s)\n"
		  (C.string_of_code stmt);
	        stmt
	      end
	  | C.Set (C.SSAReg id, (C.Binary (CT.Add, C.Entity (CT.PC loc),
					   const_exp) as rhs)) ->
	      begin try
	        let new_rhs = eval_minipool_const meta rhs in
	        Log.printf 3
		  "Formed constant address for minipool entry (%lx)\n" new_rhs;
		Typedb.record_impl inforec.Typedb.implications id
		  Typedb.Pointer;
		C.Set (C.SSAReg id, C.Immed new_rhs)
	      with Const.Non_constant ->
	        Log.printf 3 "Didn't form address of minipool entry (%s)\n"
		  (C.string_of_code stmt);
		stmt
	      end
	  | x -> x)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr
