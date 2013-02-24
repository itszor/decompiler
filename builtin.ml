(* Some stuff is easier to handle here, i.e. by hacking, rather than trying to
   understand every nuance of the C runtime system...  *)

open Ctype
open Function

let builtin_function_type = function
    "strlen" ->
      {
        args = [| C_const (C_pointer C_char) |];
	arg_locs = [| Some (Dwarfreader.Loc_expr (`DW_OP_reg 0)) |];
	arg_names = [| "str" |];
	framebase_loc = None;
	return = C_int;
	local = false;
	prototyped = true
      }
  | "memcpy" ->
      {
        args = [| C_pointer C_void; C_const (C_pointer C_void); C_int |];
	arg_locs = [| Some (Dwarfreader.Loc_expr (`DW_OP_reg 0));
		      Some (Dwarfreader.Loc_expr (`DW_OP_reg 1));
		      Some (Dwarfreader.Loc_expr (`DW_OP_reg 2)) |];
	arg_names = [| "dst"; "src"; "len" |];
	framebase_loc = None;
	return = C_pointer C_void;
	local = false;
	prototyped = true
      }
  | "memset" ->
      {
	args = [| C_pointer C_void; C_int; C_unsigned C_int |];
	arg_locs = [||];
	arg_names = [| "s"; "c"; "n" |];
	framebase_loc = None;
	return = C_pointer C_void;
	local = false;
	prototyped = true
      }
  | _ -> raise Not_found
