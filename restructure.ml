open Locations

module CS = Ir.IrCS
module CT = Ir.IrCT
module BS = Ir.IrBS
module C = Ir.Ir

type nesting =
    Anon_block of scope_contents
(*| For_loop of block_contents
  | Do_loop of block_contents
  | While_loop of block_contents
  | If_stmt of block_contents
  | If_else_stmt of block_contents * block_contents
  | Switch_stmt of block_contents*)

and block_or_nested =
    Block_ref of int
  | Nested of nesting

and scope_contents =
  {
    mutable locals : local_var list;
    bbs_in_scope : block_or_nested list;
  }

and local_var =
  {
    var_name : string;
    var_type : Ctype.ctype;
    var_initialiser : C.code option;
    var_origin : origin;
    var_location : location list
  }

and origin =
    Incoming_arg
  | Local

let convert_args ft ct_for_cu =
  let locals = ref [] in
  let accum = Eabi.make_arg_accum () in
  for i = 0 to Array.length ft.Function.args - 1 do
    let name = ft.Function.arg_names.(i)
    and typ = ft.Function.args.(i)
    and loc_opt = ft.Function.arg_locs.(i) in
    match loc_opt with
      None -> failwith "need a location for an argument"
    | Some loc ->
        let local = {
	  var_name = name;
	  var_type = typ;
	  var_initialiser = None;
	  var_origin = Incoming_arg;
	  var_location = [Eabi.eabi_arg_loc ft i accum ct_for_cu]
	} in
	Log.printf 3 "arg %s, loc %s\n" local.var_name
	  (String.concat " && "
	    (List.map string_of_location local.var_location));
	locals := local :: !locals
  done;
  !locals

let restructure blk_arr ft ct_for_cu =
  let bbs_in_func = ref [] in
  for idx = Array.length blk_arr - 1 downto 0 do
    match blk_arr.(idx).Block.id with
      BS.Virtual_entry | BS.Virtual_exit -> ()
    | _ -> bbs_in_func := Block_ref idx :: !bbs_in_func
  done;
  let arg_locals = convert_args ft ct_for_cu in
  Anon_block { locals = arg_locals; bbs_in_scope = !bbs_in_func }
