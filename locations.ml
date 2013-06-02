module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type pieces =
    In of C.code
  | Parts of (C.code * int * int) list

type location =
    Everywhere of pieces
  | Within_range of (int32 * int32 * pieces) list

let rec valid_at_address addr = function
    Everywhere p -> Some p
  | Within_range ((lo, hi, p) :: more) ->
      if addr >= lo && addr < hi then Some p
      else valid_at_address addr (Within_range more)
  | _ -> None

let string_of_pieces = function
    In c -> Printf.sprintf "in %s" (C.string_of_code c)
  | Parts partlist ->
      let slist = List.map
        (fun (code, lo, size) ->
	  Printf.sprintf "%d-byte part @ offset %d in %s" size lo
			 (C.string_of_code code))
	partlist in
      String.concat ", " slist

let string_of_location = function
    Everywhere p -> string_of_pieces p
  | Within_range ranges ->
      let slist = List.map
        (fun (lo, hi, pieces) ->
	  Printf.sprintf "%s (between %lx and %lx)" (string_of_pieces pieces)
			 lo hi)
	ranges in
      String.concat "; " slist

let convert_dwarf_loc = function
    `DW_OP_reg r -> C.Reg (CT.Hard_reg r)
  | `DW_OP_fbreg o -> C.Reg (CT.Stack o)
  | `DW_OP_regx r when r >= 64 && r < 96 -> C.Reg (CT.VFP_sreg (r - 64))
  | `DW_OP_breg (r, o) ->
      C.Binary (CT.Add, C.Reg (CT.Hard_reg r),
		C.Immed (Big_int.int32_of_big_int o))
  | `DW_OP_addr addr ->
      (* FIXME: Dubious.  *)
      C.Unary (CT.Address_of, C.Immed (Int64.to_int32 addr))
  | _ -> failwith "Unknown loc expr"

let convert_dwarf_loclist = function
    Dwarfreader.Loc_expr le -> Everywhere (In (convert_dwarf_loc le))
  | Dwarfreader.Loc_list ll ->
      let ranges = List.fold_right
	(fun (lo, hi, loc) acc ->
	  let conv_loc = convert_dwarf_loc loc in
	  (lo, hi, In conv_loc) :: acc)
	ll
	[] in
      Within_range ranges

let convert_dwarf_loclist_opt = function
    None -> None
  | Some loclist -> Some (convert_dwarf_loclist loclist)

(* Find CFA offset for LOC (if it describes such an offset), returning
   int option.  *)

let loc_cfa_offset_at_addr loc addr =
  try
    match Dwarfreader.loc_for_addr addr loc with
      `DW_OP_fbreg o -> Some o
    | _ -> None
  with Not_found ->
    None
