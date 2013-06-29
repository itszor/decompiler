(* Attempt to resolve constant pointers within the program image.  *)

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

(* Try finding type info for global variable from either:
     - Dwarf info for the compilation unit.
     - Guess, based on info from type database.
   The latter isn't really expected to do well in general.
*)

let type_for_global cu_inf name id inforec ctypes_for_cu =
  try
    let vardecl = Hashtbl.find cu_inf.Binary_info.ci_globalvars name in
    vardecl.Binary_info.vardecl_type
  with Not_found ->
    Log.printf 3 "Unknown type for '%s', asking type db to choose one\n" name;
    Vartypes.choose_type ctypes_for_cu id inforec

let imageptr_resolve binf cu_inf blk_arr inforec ctypes_for_cu =
  let open Binary_info in
  let meta = Const.create_metadata blk_arr in
  Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt ->
	  C.map
	    (fun node ->
	      match node with
		C.Set (C.SSAReg id, maybe_const_expr) ->
	          begin try let symbolic_replacement =
		    let imm = Const.eval_const meta maybe_const_expr in
		    let pointer_p = Typedb.probably_pointer ctypes_for_cu id
							    inforec in
		    if pointer_p then begin
		      Log.printf 3 "immediate value is used as pointer\n";
		      try
			let sym =
			  Symbols.find_symbol_by_addr
			    ~filter:(fun symbol ->
			      Symbols.symbol_type symbol <> Symbols.STT_NOTYPE
			      || Symbols.symbol_binding symbol
				 <> Symbols.STB_LOCAL)
			    binf.symbols imm in
			let symname = Symbols.symbol_name sym binf.strtab in
			let offset = Int32.sub imm sym.Elfreader.st_value in
			Log.printf 3
			  "looks like symbol '%s' (size %ld, +%ld bytes)\n"
			  symname sym.Elfreader.st_size offset;
			let base =
			  C.Entity (CT.Symbol_ref (symname, sym)) in
			let symtype =
			  type_for_global cu_inf symname id inforec
					  ctypes_for_cu in
			Log.printf 3 "Using type '%s'\n"
			  (Ctype.string_of_ctype symtype);
			(*Typedb.record_info inforec.Typedb.infotag id
			  (Typedb.Known_ptr_type_offset (symtype, offset));*)
			(*let access =
			  Ptrtracking.stackvar_access base symtype offset
			    ctypes_for_cu in
			  C.Unary (CT.Address_of, access) *)
			C.Unary (CT.Address_of,
				 C.Binary (CT.Raw_offset symtype, base,
					   C.Immed offset))
		      with Not_found ->
			let pointed_to_sec_num =
			  Elfreader.get_section_num_by_addr binf.elfbits
			    binf.ehdr binf.shdr_arr imm in
			let pointed_to_sec_name =
			  Elfreader.get_section_name binf.elfbits binf.ehdr
			    binf.shdr_arr pointed_to_sec_num in
			Log.printf 3 "pointer but no symbol for address\n";
			Log.printf 3 "section name is %s\n" pointed_to_sec_name;
			let sec_base =
			  binf.shdr_arr.(pointed_to_sec_num).Elfreader
			    .sh_addr in
			Log.printf 3 "section base: %lx\n" sec_base;
			let offset = Int32.sub imm sec_base in
			Log.printf 3 "offset into section %ld\n" offset;
			(* FIXME: Special section+offset, then print section as
			   char array?  Better to use coverage -- split rodata
			   up into pieces, the best we can, after we've
			   converted all the code in the binary.  We can also
			   make use of any symbols defined in the section,
			   which helpfully also have sizes.  *)
			C.Binary (CT.Add,
				  C.Entity (CT.Section pointed_to_sec_name),
				  C.Immed offset)
		    end else begin
		      Log.printf 3 "register loaded is not used as pointer\n";
		      maybe_const_expr
		    end in
		    C.Set (C.SSAReg id, symbolic_replacement)
		  with Const.Non_constant ->
		    node
		  end
	      | _ -> node)
	    stmt)
	  blk.Block.code in
      { blk with Block.code = code' })
    blk_arr

(*let resolve_raw_offsets binf cu_inf blk_arr inforec ctypes_for_cu =
  Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt ->
	  C.map
	    (fun node ->
	      match node with
	        C.Unary (accsz, addr) ->)
	    stmt)
        blk.Block.code in
      { blk with Block.code = code' })
    blk_arr*)
