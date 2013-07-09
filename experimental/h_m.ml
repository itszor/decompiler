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

let resolve_type ht subst typ =
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
  lookup typ

exception Type_mismatch of T.node_type * T.node_type
exception Occurs_check of int * T.node_type

module IntSet = Set.Make (struct
  type t = int
  let compare = compare
end)

let imply t =
  let open T in
  let i = ref 0 in
  let new_typevar () = incr i; !i in
  let new_type () = TyVar (new_typevar ()) in
  let ht = Hashtbl.create 10
  and subst = Hashtbl.create 10 in
  let rec occurs_raw tyvar = function
    Int | Bool -> false
  | List t -> occurs_raw tyvar t
  | Arrow (a, b) -> occurs_raw tyvar a || occurs_raw tyvar b
  | TyVar tv -> tv = tyvar
  and occurs tyvar typ =
    occurs_raw (find_subst subst tyvar) (resolve_type ht subst typ)
  and occurs_in_set tyvar tset =
    IntSet.exists (fun typ -> occurs tyvar (TyVar typ)) tset
  and add_subst a b =
    if a <> b then begin
      let lower = min a b
      and higher = max a b in
      if Hashtbl.mem subst higher then
	unify (TyVar (Hashtbl.find subst higher)) (TyVar lower)
      else
	Hashtbl.add subst higher lower
    end
  and unify ?a ?b t1 t2 =
    Printf.printf "%s === %s\n" (string_of_type t1)
		  (string_of_type t2);
    begin match a with
      None -> ()
    | Some a -> Printf.printf "A: %s\n" (U.string_of_expr a)
    end;
    begin match b with
      None -> ()
    | Some a -> Printf.printf "B: %s\n" (U.string_of_expr a)
    end;
    match resolve_type ht subst t1, resolve_type ht subst t2 with
      TyVar a, TyVar b when a <> b -> add_subst a b
    | TyVar a, other
    | other, TyVar a ->
        let a' = find_subst subst a in
	if occurs a' other then begin
	  Printf.printf "'t%d occurs in %s\n" a' (string_of_type other);
	  raise (Occurs_check (a', other))
	end else if Hashtbl.mem ht a' then begin
	  let prevtype = Hashtbl.find ht a' in
	  Printf.printf "Unifying with previous for %d (%d) (%s / %s)\n" a' a
	    (string_of_type prevtype) (string_of_type other);
	  (* It's very important that here PREVTYPE and OTHER are not both
	     plain TyVars!  *)
	  unify prevtype other
	end else
	  Hashtbl.add ht a' other
    | Int, Int
    | Bool, Bool -> ()
    | List l1, List l2 -> unify l1 l2
    | Arrow (a1, a2), Arrow (b1, b2) -> unify a1 b1; unify a2 b2
    | t1, t2 -> raise (Type_mismatch (t1, t2)) in
  let inst bound typ =
    let newtvs = Hashtbl.create 5 in
    let rec inst' typ =
      match typ with
	Int | Bool -> typ
      | List t -> List (inst' t)
      | Arrow (a, b) -> Arrow (inst' a, inst' b)
      | TyVar tv ->
          if not (occurs_in_set tv bound) then begin
	    if not (Hashtbl.mem newtvs tv) then
	      Hashtbl.add newtvs tv (new_typevar ());
	    TyVar (Hashtbl.find newtvs tv)
	  end else
	    typ in
    inst' (resolve_type ht subst typ) in
  let generalise ctx t =
    let newtvs = Hashtbl.create 5 in
    let res_type = resolve_type ht subst t in
    let rec gen' t =
      match t with
        Int | Bool -> t
      | List t -> List (gen' t)
      | Arrow (a, b) -> Arrow (gen' a, gen' b)
      | TyVar tv ->
	  if List.exists (fun (_, typ) -> occurs tv typ) ctx then begin
	    if not (Hashtbl.mem newtvs tv) then
	      Hashtbl.add newtvs tv (new_typevar ());
	    TyVar (Hashtbl.find newtvs tv)
	  end else
	    t in
    gen' res_type in
  let rec imply' ctx bound t =
    try
      match t with
	U.Zero -> Typed (Int, Zero)
      | U.True -> Typed (Bool, True)
      | U.False -> Typed (Bool, False)
      | U.Id x -> Typed (inst bound (List.assoc x ctx), Id x)
      | U.Pred a ->
	  let Typed (ta, a') = imply' ctx bound a in
	  unify ~a:a ta Int;
	  Typed (Int, Pred (Typed (ta, a')))
      | U.Succ a ->
	  let Typed (ta, a') = imply' ctx bound a in
	  unify ~a:a ta Int;
	  Typed (Int, Succ (Typed (ta, a')))
      | U.IsZero a ->
	  let Typed (ta, a') = imply' ctx bound a in
	  unify ~a:a ta Int;
	  Typed (Bool, IsZero (Typed (ta, a')))
      | U.Cons (a, b) ->
          let Typed (ta, a') = imply' ctx bound a in
	  let Typed (tb, b') = imply' ctx bound b in
	  let nt = new_type () in
	  unify ~a:a nt ta;
	  unify (List nt) tb;
	  Typed (List nt, Cons (Typed (ta, a'), Typed (tb, b')))
      | U.Car a ->
          let Typed (ta, a') = imply' ctx bound a in
	  let nt = new_type () in
	  unify ~a:a ta (List nt);
	  Typed (nt, Car (Typed (ta, a')))
      | U.Cdr a ->
	  let Typed (ta, a') = imply' ctx bound a in
	  let nt = new_type () in
	  unify ~a:a ta (List nt);
	  Typed (ta, Cdr (Typed (ta, a')))
      | U.Nil ->
	  let nt = new_type () in
          Typed (List nt, Nil)
      | U.Null a ->
	  let Typed (ta, a') = imply' ctx bound a in
	  let nt = new_type () in
	  unify ~a:a ta (List nt);
	  Typed (Bool, Null (Typed (ta, a')))
      | U.IfThenElse (a, b, c) ->
	  let Typed (ta, a') = imply' ctx bound a in
	  let Typed (tb, b') = imply' ctx bound b in
	  let Typed (tc, c') = imply' ctx bound c in
	  unify ~a:b ~b:c tb tc;
	  unify ~a:a ta Bool;
	  Typed (tb, IfThenElse (Typed (ta, a'), Typed (tb, b'),
		 Typed (tc, c')))
      | U.Fun (x, a) ->
	  let vartype = new_typevar () in
	  let bound' = IntSet.add vartype bound in
	  let Typed (ta, a') = imply' ((x, TyVar vartype) :: ctx) bound' a in
	  Typed (Arrow (TyVar vartype, ta), Fun (x, Typed (ta, a')))
      | U.Apply (a, b) ->
	  let Typed (ta, a') = imply' ctx bound a in
	  let Typed (tb, b') = imply' ctx bound b in
	  let nt1 = new_type () in
	  unify ~a:a ~b:b ta (Arrow (tb, nt1));
	  Typed (nt1, Apply (Typed (ta, a'), Typed (tb, b')))
      | U.LetIn (x, a, b) ->
          let Typed (ta, a') = imply' ctx bound a in
	  Printf.printf "ta = %s\n" (string_of_type (resolve_type ht subst ta));
	  let vartype = generalise ctx ta in
	  Printf.printf "ta (gen) = %s\n" (string_of_type vartype);
	  let addvar = (x, vartype) :: ctx in
	  let Typed (tb, b') = imply' addvar bound b in
	  Printf.printf "tb = %s\n" (string_of_type tb);
	  Typed (tb, LetIn (x, Typed (ta, a'), Typed (tb, b')))
    with Occurs_check (tv, typ) ->
      Printf.printf "when unifying %s\n" (U.string_of_expr t);
      failwith "Stop."
    in
  let typed_expr = imply' [] IntSet.empty t in
  typed_expr, ht, subst

let rec rewrite_types ht subst typed_expr =
  let open T in
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
  Typed (resolve_type ht subst t1, expr')

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

let expr1 =
  let open U in
  LetIn ("z", Zero, LetIn ("x", Fun ("y", Id "z"),
    Cons (Apply (Id "x", False), Cons (Apply (Id "x", Zero), Nil))))

let _ =
  doit degen2
