(* Slice up a section.  *)

open Symbols

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

let slice blk_arr coverage sec_base sec_name =
  Array.iter
    (fun blk ->
      CS.iter
        (fun stmt ->
	  C.iter
	    (function
	      C.Binary (Irtypes.Add, C.Entity (CT.Section nm), C.Immed imm) ->
	        if sec_name = nm then begin
	          let addr = Int32.add sec_base imm in
		  Coverage.add_range coverage (Coverage.Half_open ("", addr))
		end
	    | _ -> ())
	  stmt)
	blk.Block.code)
    blk_arr

let symbols coverage symbols strtab sec_num =
  List.iter
    (fun sym ->
      let addr = sym.Elfreader.st_value
      and size = sym.Elfreader.st_size
      and name = symbol_name sym strtab in
      Coverage.add_range coverage (Coverage.Range (name, addr, size)))
    (Symbols.symbols_for_section symbols sec_num)
