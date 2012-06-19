module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

exception Substitution

let try_substitute rodata typ start length base offset =
  match typ with
    Slice_section.Anonymous _ ->
      if (Int32.sub start base) = offset then begin
        let str = Elfreader.get_string rodata (Int32.to_int offset) in
	if (String.length str + 4) land (lnot 3) = Int32.to_int length then
	  C.Entity (CT.String_constant str)
	else
	  raise Substitution
      end else
        raise Substitution
  | _ -> raise Substitution

let resolve blk_arr rodata rodata_coverage =
  Array.map
    (fun blk ->
      let code' = CS.map
        (fun stmt ->
	  C.map
	    (function
	      C.Binary (Irtypes.Add,
			C.Entity (CT.Section secnm), C.Immed offset) as x ->
		begin try
		  match secnm with
		    ".rodata" ->
		      let base = rodata_coverage.Coverage.start in
		      let addr = Int32.add base offset in
		      let range =
			Coverage.find_closed_range rodata_coverage addr in
		      begin match range with
			Coverage.Range (typ, start, length)
		      | Coverage.Padded_range (typ, start, _, length) ->
			  try_substitute rodata typ start length base offset
		      | _ -> failwith "open range"
		      end
		  | x -> failwith ("unknown section " ^ x)
		with Substitution ->
		  x
		end
	    | x -> x)
	    stmt)
	blk.Block.code in
      { blk with Block.code = code' })
    blk_arr
