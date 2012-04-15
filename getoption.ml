let get_option = function
    Some x -> x
  | None -> raise (Failure "get_option")
