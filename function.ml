open Ctype

type function_info =
  {
    args : ctype array;
    return : ctype
  }

let type_for_function name =
  match name with
    "foo" ->
      { args = [| C_int; C_int; C_int; C_int; C_int; C_int |];
        return = C_int }
  | "blah" ->
      { args = [| C_int; C_int |];
        return = C_int }
  | "blah2" ->
      { args = [| C_pointer C_int |];
        return = C_int }
  | "main" ->
      { args = [| |];
        return = C_int }
  | "loop" ->
      { args = [| C_int |];
        return = C_int }
  | _ -> raise Not_found
