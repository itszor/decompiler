module CS = Ir.IrCS
module CT = Ir.IrCT
module C = Ir.Ir

type location =
    Parts of (int * int * location) list
  | Within_range of int32 * int32 * location
  | In of C.code

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
