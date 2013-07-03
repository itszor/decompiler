module U = struct
  type expr =
      Zero
    | True
    | False
    | Id of string
    | Pred of expr
    | Succ of expr
    | IsZero of expr
    | Cons of expr * expr
    | Car of expr
    | Cdr of expr
    | Nil
    | Null of expr
    | IfThenElse of expr * expr * expr
    | Fun of string * expr
    | Apply of expr * expr
    | LetIn of string * expr * expr

  let rec string_of_expr = function
    Zero -> "0"
  | True -> "true"
  | False -> "false"
  | Id x -> x
  | Pred x -> Printf.sprintf "pred %s" (string_of_expr x)
  | Succ x -> Printf.sprintf "succ %s" (string_of_expr x)
  | IsZero x -> Printf.sprintf "iszero %s" (string_of_expr x)
  | Cons (a, b) -> Printf.sprintf "%s :: %s" (string_of_expr a)
		     (string_of_expr b)
  | Car a -> Printf.sprintf "car %s" (string_of_expr a)
  | Cdr a -> Printf.sprintf "cdr %s" (string_of_expr a)
  | Nil -> "[]"
  | Null a -> Printf.sprintf "null %s" (string_of_expr a)
  | IfThenElse (a, b, c) ->
      Printf.sprintf "if %s then %s else %s" (string_of_expr a)
	(string_of_expr b) (string_of_expr c)
  | Fun (x, a) ->
      Printf.sprintf "fun %s -> %s" x (string_of_expr a)
  | Apply (a, b) ->
      Printf.sprintf "(%s %s)" (string_of_expr a)
		     (string_of_expr b)
  | LetIn (x, a, b) ->
      Printf.sprintf "let %s = %s in %s" x (string_of_expr a)
		     (string_of_expr b)
end

module T = struct
  type expr =
      Zero
    | True
    | False
    | Id of string
    | Pred of typed_expr
    | Succ of typed_expr
    | IsZero of typed_expr
    | Cons of typed_expr * typed_expr
    | Car of typed_expr
    | Cdr of typed_expr
    | Nil
    | Null of typed_expr
    | IfThenElse of typed_expr * typed_expr * typed_expr
    | Fun of string * typed_expr
    | Apply of typed_expr * typed_expr
    | LetIn of string * typed_expr * typed_expr

  and typed_expr =
      Typed of node_type * expr

  and node_type =
      Int
    | Bool
    | List of node_type
    | Arrow of node_type * node_type
    | TyVar of int
  
  let rec string_of_expr = function
    Zero -> "0"
  | True -> "true"
  | False -> "false"
  | Id x -> x
  | Pred x -> Printf.sprintf "pred %s" (string_of_texpr x)
  | Succ x -> Printf.sprintf "succ %s" (string_of_texpr x)
  | IsZero x -> Printf.sprintf "iszero %s" (string_of_texpr x)
  | Cons (a, b) -> Printf.sprintf "%s :: %s" (string_of_texpr a)
		     (string_of_texpr b)
  | Car a -> Printf.sprintf "car %s" (string_of_texpr a)
  | Cdr a -> Printf.sprintf "cdr %s" (string_of_texpr a)
  | Nil -> "[]"
  | Null a -> Printf.sprintf "null %s" (string_of_texpr a)
  | IfThenElse (a, b, c) ->
      Printf.sprintf "if %s then %s else %s" (string_of_texpr a)
	(string_of_texpr b) (string_of_texpr c)
  | Fun (x, a) ->
      Printf.sprintf "fun %s -> %s" x (string_of_texpr a)
  | Apply (a, b) ->
      Printf.sprintf "(%s %s)" (string_of_texpr a)
		     (string_of_texpr b)
  | LetIn (x, a, b) ->
      Printf.sprintf "let %s = %s in %s" x (string_of_texpr a)
		     (string_of_texpr b)

  and string_of_texpr (Typed (t, x)) =
    Printf.sprintf "(%s : %s)" (string_of_expr x) (string_of_type t)
  
  and string_of_type ?(bracket=false) = function
    Int -> "int"
  | Bool -> "bool"
  | List x -> Printf.sprintf "%s list" (string_of_type x)
  | Arrow (a, b) ->
      if bracket then
        Printf.sprintf "(%s -> %s)" (string_of_type ~bracket:true a)
	  (string_of_type b)
      else
        Printf.sprintf "%s -> %s" (string_of_type ~bracket:true a)
	  (string_of_type b)
  | TyVar t -> Printf.sprintf "'t%d" t
end

let rec find_subst subst_tab a =
  try
    find_subst subst_tab (Hashtbl.find subst_tab a)
  with Not_found ->
    a

let rec subst_tyvars subst = function
    T.TyVar t -> T.TyVar (find_subst subst t)
  | T.List t -> T.List (subst_tyvars subst t)
  | T.Arrow (a, b) -> T.Arrow (subst_tyvars subst a, subst_tyvars subst b)
  | x -> x

exception Type_mismatch of T.node_type * T.node_type
exception Occurs_check of int * T.node_type

let imply t =
  let open T in
  let i = ref 0 in
  let new_type () =
    incr i;
    T.TyVar !i in
  let ht = Hashtbl.create 10
  and subst = Hashtbl.create 10 in
  let rec occurs tyvar = function
    Int | Bool -> false
  | List t -> occurs tyvar t
  | Arrow (a, b) -> occurs tyvar a || occurs tyvar b
  | TyVar tv -> find_subst subst tv = tyvar
  and add_subst a b =
    Printf.printf "add_subst %d %d\n" a b;
    let a' = find_subst subst a
    and b' = find_subst subst b in
    if a' <> b' then begin
      Printf.printf "actually adding %d %d\n" a' b';
      Hashtbl.add subst a' b';
      if Hashtbl.mem ht a then begin
	let oldtype = Hashtbl.find ht a in
	Printf.printf "Detaching %s from %d\n" (T.string_of_type oldtype) a;
	Hashtbl.remove ht a;
	Printf.printf "Re-unifying to %d\n" b';
	unify (TyVar b') (resolve_types oldtype)
      end
    end
  and resolve_types t =
    match t with
      Int | Bool -> t
    | List t -> List (resolve_types t)
    | Arrow (a, b) -> Arrow (resolve_types a, resolve_types b)
    | TyVar tv ->
        begin try
	  Hashtbl.find ht (find_subst subst tv)
	with Not_found ->
	  TyVar (find_subst subst tv)
	end
  and unify t1 t2 =
    Printf.printf "%s === %s\n" (string_of_type t1)
		  (string_of_type t2);
    match t1, t2 with
      TyVar a, TyVar b ->
        add_subst a b
    | TyVar a, other
    | other, TyVar a ->
        let a' = find_subst subst a in
	if occurs a' (resolve_types other) then begin
	  Printf.printf "'t%d occurs in %s\n" a'
	    (string_of_type (resolve_types other));
	  raise (Occurs_check (a', (resolve_types other)))
	end else if Hashtbl.mem ht a' then begin
	  let prevtype = Hashtbl.find ht a' in
	  Printf.printf "Unifying with previous for %d (%d) (%s / %s)\n" a' a
	    (string_of_type prevtype) (string_of_type other);
	  (* It's very important that here PREVTYPE and OTHER are not both
	     plain TyVars!  *)
	  unify (resolve_types prevtype) (resolve_types other)
	end else
	  Hashtbl.add ht a' (resolve_types other)
    | Int, Int
    | Bool, Bool -> ()
    | List l1, List l2 -> unify l1 l2
    | Arrow (a1, a2), Arrow (b1, b2) -> unify a1 b1; unify a2 b2
    | t1, t2 -> raise (Type_mismatch (t1, t2)) in
  let rec imply' ctx t =
    try
      match t with
	U.Zero -> Typed (Int, Zero)
      | U.True -> Typed (Bool, True)
      | U.False -> Typed (Bool, False)
      | U.Id x -> Typed (List.assoc x ctx, Id x)
      | U.Pred a ->
	  let Typed (ta, a') = imply' ctx a in
	  unify ta Int;
	  Typed (Int, Pred (Typed (ta, a')))
      | U.Succ a ->
	  let Typed (ta, a') = imply' ctx a in
	  unify ta Int;
	  Typed (Int, Succ (Typed (ta, a')))
      | U.IsZero a ->
	  let Typed (ta, a') = imply' ctx a in
	  unify ta Int;
	  Typed (Bool, IsZero (Typed (ta, a')))
      | U.Cons (a, b) ->
          let Typed (ta, a') = imply' ctx a in
	  let Typed (tb, b') = imply' ctx b in
	  let nt = new_type () in
	  unify nt ta;
	  unify (List nt) tb;
	  Typed (List nt, Cons (Typed (ta, a'), Typed (tb, b')))
      | U.Car a ->
          let Typed (ta, a') = imply' ctx a in
	  let nt = new_type () in
	  unify ta (List nt);
	  Typed (nt, Car (Typed (ta, a')))
      | U.Cdr a ->
	  let Typed (ta, a') = imply' ctx a in
	  let nt = new_type () in
	  unify ta (List nt);
	  Typed (ta, Cdr (Typed (ta, a')))
      | U.Nil ->
	  let nt = new_type () in
          Typed (List nt, Nil)
      | U.Null a ->
	  let Typed (ta, a') = imply' ctx a in
	  let nt = new_type () in
	  unify ta (List nt);
	  Typed (Bool, Null (Typed (ta, a')))
      | U.IfThenElse (a, b, c) ->
	  let Typed (ta, a') = imply' ctx a in
	  let Typed (tb, b') = imply' ctx b in
	  let Typed (tc, c') = imply' ctx c in
	  unify tb tc;
	  unify ta Bool;
	  Typed (tb, IfThenElse (Typed (ta, a'), Typed (tb, b'),
		 Typed (tc, c')))
      | U.Fun (x, a) ->
	  let vartype = new_type () in
	  let Typed (ta, a') = imply' ((x, vartype) :: ctx) a in
	  Typed (Arrow (vartype, ta), Fun (x, Typed (ta, a')))
      | U.Apply (a, b) ->
	  let Typed (ta, a') = imply' ctx a in
	  let Typed (tb, b') = imply' ctx b in
	  let nt1 = new_type () in
	  unify ta (Arrow (tb, nt1));
	  Typed (nt1, Apply (Typed (ta, a'), Typed (tb, b')))
      | U.LetIn (x, a, b) ->
	  let vartype = new_type () in
	  let addvar = (x, vartype) :: ctx in
          let Typed (ta, a') = imply' ctx a in
	  let Typed (tb, b') = imply' addvar b in
	  Printf.printf "ta = %s\n" (string_of_type ta);
	  Printf.printf "tb = %s\n" (string_of_type tb);
	  Printf.printf "vartype = %s\n" (string_of_type vartype);
	  unify vartype ta;
	  Typed (tb, LetIn (x, Typed (ta, a'), Typed (tb, b')))
    with Occurs_check (tv, typ) ->
      Printf.printf "when unifying %s\n" (U.string_of_expr t);
      failwith "Stop."
    in
  let typed_expr = imply' [] t in
  typed_expr, ht, subst

let rec rewrite_types ht subst typed_expr =
  let open T in
  let rec lookup t =
    match t with
      TyVar t1 ->
        begin try
	  lookup (Hashtbl.find ht (find_subst subst t1))
	with Not_found ->
	  TyVar (find_subst subst t1)
	end
    | List t -> List (lookup t)
    | Arrow (a, b) -> Arrow (lookup a, lookup b)
    | x -> x in
  let Typed (t1, expr) = typed_expr in
  let expr' =
    match expr with
      Zero | True | False | Id _ | Nil -> expr
    | Pred x -> Pred (rewrite_types ht subst x)
    | Succ x -> Succ (rewrite_types ht subst x)
    | IsZero x -> IsZero (rewrite_types ht subst x)
    | Cons (x, y) -> Cons (rewrite_types ht subst x, rewrite_types ht subst y)
    | Car x -> Car (rewrite_types ht subst x)
    | Cdr x -> Cdr (rewrite_types ht subst x)
    | Null x -> Null (rewrite_types ht subst x)
    | IfThenElse (a, b, c) -> IfThenElse (rewrite_types ht subst a,
					  rewrite_types ht subst b,
					  rewrite_types ht subst c)
    | Fun (x, a) -> Fun (x, rewrite_types ht subst a)
    | Apply (a, b) -> Apply (rewrite_types ht subst a, rewrite_types ht subst b)
    | LetIn (x, a, b) -> LetIn (x, rewrite_types ht subst a,
				rewrite_types ht subst b) in
  Typed (lookup t1, expr')

let doit expr =
  try
    let typed, ht, subst = imply expr in
    Hashtbl.iter
      (fun i t ->
	Printf.printf "Mapping for 't%d = %s\n" i (T.string_of_type t)) ht;
    Hashtbl.iter
      (fun i t ->
	Printf.printf "Substitution 't%d = 't%d\n" i t) subst;
    Hashtbl.iter
      (fun i t ->
	Printf.printf "Subst map for 't%d = %s\n" i
	  (T.string_of_type (subst_tyvars subst t))) ht;
    rewrite_types ht subst typed
  with Type_mismatch (a, b) ->
    Printf.fprintf stderr "Type mismatch (%s vs %s)\n" (T.string_of_type a)
		   (T.string_of_type b);
    flush stderr;
    failwith "stop."

let typeof (T.Typed (t, _)) = t

let degen =
  let open U in
  LetIn ("pair", Fun ("x", Fun ("y", Fun ("z",
		   Apply (Apply (Id "z", Id "x"), Id "y")))),
  LetIn ("x1", Fun ("y", Apply (Apply (Id "pair", Id "y"), Id "y")),
    LetIn ("x2", Fun ("y", Apply (Id "x1", Apply (Id "x1", Id "y"))),
      LetIn ("x3", Fun ("y", Apply (Id "x2", Apply (Id "x2", Id "y"))),
        LetIn ("x4", Fun ("y", Apply (Id "x3", Apply (Id "x3", Id "y"))),
	  Apply (Id "x4", Fun ("z", Id "z")))))))

let degen2 =
  let open U in
  LetIn ("pair", Fun ("x", Fun ("y", Fun ("z",
		   Apply (Apply (Id "z", Id "x"), Id "y")))),
  LetIn ("x1", Fun ("y", Apply (Apply (Id "pair", Id "y"), Id "y")),
    Fun ("y", Apply (Id "x1", Apply (Id "x1", Id "y")))))

let _ =
  doit degen2
