(* Slice up a section.  *)

open Symbols

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

type slicetype =
    Symbol of Elfreader.elf_sym
  | Anonymous of string

let slice blk_arr coverage sec_base sec_name fn_name =
  Array.iter
    (fun blk ->
      CS.iter
        (fun stmt ->
	  C.iter
	    (function
	      C.Binary (CT.Add, C.Entity (CT.Section nm), C.Immed imm) ->
	        if sec_name = nm then begin
	          let addr = Int32.add sec_base imm in
		  let anon_name = Printf.sprintf "%s$anon%lx" fn_name addr in
		  Coverage.add_range coverage
		    (Coverage.Half_open (Anonymous anon_name, addr))
		end
	    | _ -> ())
	  stmt)
	blk.Block.code)
    blk_arr

let symbols coverage symbols strtab sec_num =
  List.iter
    (fun sym ->
      let addr = sym.Elfreader.st_value
      and size = sym.Elfreader.st_size in
      if not (Mapping.is_mapping_symbol sym) then
	Coverage.add_range coverage (Coverage.Range (Symbol sym, addr, size)))
    (Symbols.symbols_for_section symbols sec_num)
