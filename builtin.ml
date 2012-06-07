open Ctype
open Function

let builtin_function_type = function
    "memset" ->
      {
	args = [| C_pointer C_char; C_int; C_int |];
	return = C_void;
	local = false;
	prototyped = true
      }
  | _ -> raise Not_found
