(* This crazy hack will be replaced with something which loads debug info from
   dependent libraries...  *)

open Ctype
open Function

let builtin_function_type = function
    "memset" ->
      {
	args = [| C_pointer C_char; C_int; C_int |];
	arg_locs = [| Some (Dwarfreader.Loc_expr (`DW_OP_reg 0));
		      Some (Dwarfreader.Loc_expr (`DW_OP_reg 1));
		      Some (Dwarfreader.Loc_expr (`DW_OP_reg 2)) |];
	arg_names = [| "x"; "y"; "z" |];
	framebase_loc = None;
	return = C_void;
	local = false;
	prototyped = true
      }
  | "puts" ->
      {
        args = [| C_pointer C_char |];
	arg_locs = [| Some (Dwarfreader.Loc_expr (`DW_OP_reg 0)) |];
	arg_names = [| "x" |];
	framebase_loc = None;
	return = C_int;
	local = false;
	prototyped = true
      }
  | _ -> raise Not_found
