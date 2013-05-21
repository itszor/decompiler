module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type location =
    Parts of (int * int * location) list
  | Within_range of int32 * int32 * location
  | In of C.code

let rec valid_at_address addr = function
    In c -> Some c
  | Within_range (lo, hi, c) when addr >= lo && addr < hi ->
      valid_at_address addr c
  | Within_range (_, _, _) -> None
  | Parts _ -> failwith "unimplemented" (* The location type is all wrong! *)

let string_of_location loc =
  let rec build = function
    In c -> Printf.sprintf "in %s" (C.string_of_code c)
  | Within_range (lo, hi, loc) ->
      Printf.sprintf "%s (between %lx and %lx)" (build loc) lo hi
  | Parts partlist ->
      let slist = List.map
        (fun (lo, size, loc) ->
	  Printf.sprintf "%d-byte part @ offset %d in %s" size lo (build loc))
	partlist in
      String.concat ", " slist in
  build loc

let convert_dwarf_loc = function
    `DW_OP_reg r -> C.Reg (CT.Hard_reg r)
  | `DW_OP_fbreg o -> C.Reg (CT.Stack o)
  | `DW_OP_regx r when r >= 64 && r < 96 -> C.Reg (CT.VFP_sreg (r - 64))
  | `DW_OP_breg (r, o) ->
      C.Binary (Irtypes.Add, C.Reg (CT.Hard_reg r),
		C.Immed (Big_int.int32_of_big_int o))
  | `DW_OP_addr addr ->
      (* FIXME: Dubious.  *)
      C.Unary (Irtypes.Address_of, C.Immed (Int64.to_int32 addr))
  | _ -> failwith "Unknown loc expr"

let convert_dwarf_loclist = function
    Dwarfreader.Loc_expr le -> [In (convert_dwarf_loc le)]
  | Dwarfreader.Loc_list ll ->
      List.fold_right
	(fun (lo, hi, loc) acc ->
	  let conv_loc = convert_dwarf_loc loc in
	  Within_range (lo, hi, In conv_loc) :: acc)
	ll
	[]

let convert_dwarf_loclist_opt = function
    None -> []
  | Some loclist -> convert_dwarf_loclist loclist

(* Find CFA offset for LOC (if it describes such an offset), returning
   int option.  *)

let loc_cfa_offset_at_addr loc addr =
  try
    match Dwarfreader.loc_for_addr addr loc with
      `DW_OP_fbreg o -> Some o
    | _ -> None
  with Not_found ->
    None
