open Structs
open VariableUtils

let stmt_to_exp_ty = function
  | { exp = e; judge = TypeOf t } -> (e, t)
  | _ -> failwith "UnTyped"

let rec substitute oldname new_expr expr =
  let rr = substitute oldname new_expr in
  match expr with
  | Name x -> if x = oldname then new_expr else Name x
  | And (l, r) -> And (rr l, rr r)
  | Or (l, r) -> Or (rr l, rr r)
  | Impl (l, r) -> Impl (rr l, rr r)
  | Pair (l, r) -> Pair (rr l, rr r)
  | First e -> First (rr e)
  | Second e -> Second (rr e)
  | Application (l, r) -> Application (rr l, rr r)
  | Lambda (arg, body) ->
      if arg = oldname then Lambda (arg, body) else Lambda (arg, rr body)
  | Mu (arg, body) -> if arg = oldname then Mu (arg, body) else Mu (arg, rr body)
  | LetPair (x, y, p, b) ->
      if x = oldname || y = oldname then LetPair (x, y, rr p, b)
      else LetPair (x, y, rr p, rr b)
  | InjectLeft (t, e) -> InjectLeft (t, rr e)
  | InjectRight (t, e) -> InjectRight (t, rr e)
  | Case (x, (x1, b1), (x2, b2)) ->
      let left = if x1 = oldname then (x1, b1) else (x1, rr b1) in
      let right = if x2 = oldname then (x2, b2) else (x2, rr b2) in
      Case (rr x, left, right)
  | Not e -> Not (rr e)
  | NAnd (l, r) -> NAnd (rr l, rr r)
  | Predicate (n, e) -> Predicate (n, List.map rr e)
  | ForAll (n, t, e) -> ForAll (n, t, rr e)
  | Exists (n, t, e) -> Exists (n, t, rr e)
  | EvaluationContext (e, v) -> EvaluationContext (rr e, rr v)
  | Command (CVar l, r) ->
      if l = oldname then Command (CVar l, r) else Command (CVar l, rr r)
  | Command (CTop, r) -> Command (CTop, rr r)
  | Top -> Top
  | Bottom -> Bottom
  | Abort -> Abort
  | Control -> Control
  | CallCC -> CallCC
  | TypeUnit -> TypeUnit
  | Let (x, e1, e2) ->
      if x = oldname then Let (x, substitute oldname new_expr e1, e2)
      else
        Let (x, substitute oldname new_expr e1, substitute oldname new_expr e2)
  | _ ->
      failwith
        (Format.asprintf "Subtitution failed for: %s"
           (PrettyPrinter.literal_expr expr))

let rec substitute_proofs oldname new_expr
    { con = c; term = { judge = j; exp = e }; inf = i } =
  match !i with
  | Inference (i, pfs) ->
      {
        con = c;
        term = { judge = j; exp = substitute oldname new_expr e };
        inf =
          ref (Inference (i, List.map (substitute_proofs oldname new_expr) pfs));
      }
  | _ ->
      {
        con = c;
        term = { judge = j; exp = substitute oldname new_expr e };
        inf = i;
      }

let rec substituteCommand comName arg expr =
  let rr = substituteCommand comName arg in
  match expr with
  | And (l, r) -> And (rr l, rr r)
  | Or (l, r) -> Or (rr l, rr r)
  | Impl (l, r) -> Impl (rr l, rr r)
  | Pair (l, r) -> Pair (rr l, rr r)
  | First e -> First (rr e)
  | Second e -> Second (rr e)
  | Application (l, r) -> Application (rr l, rr r)
  | Lambda (arg, body) ->
      if arg = comName then Lambda (arg, body) else Lambda (arg, rr body)
  | Mu (arg, body) -> if arg = comName then Mu (arg, body) else Mu (arg, rr body)
  | LetPair (x, y, p, b) ->
      if x = comName || y = comName then LetPair (x, y, rr p, b)
      else LetPair (x, y, rr p, rr b)
  | InjectLeft (t, e) -> InjectLeft (t, rr e)
  | InjectRight (t, e) -> InjectRight (t, rr e)
  | Case (x, (x1, b1), (x2, b2)) ->
      let left = if x1 = comName then (x1, b1) else (x1, rr b1) in
      let right = if x2 = comName then (x2, b2) else (x2, rr b2) in
      Case (rr x, left, right)
  | Not e -> Not (rr e)
  | NAnd (l, r) -> NAnd (rr l, rr r)
  | Predicate (n, e) -> Predicate (n, List.map rr e)
  | ForAll (n, t, e) -> ForAll (n, t, rr e)
  | Exists (n, t, e) -> Exists (n, t, rr e)
  | EvaluationContext (e, v) -> EvaluationContext (rr e, rr v)
  | Command (CVar v, l) ->
      if v = comName then Command (CVar v, Application (rr l, rr arg))
      else Command (CVar v, rr l)
  | Command (CTop, l) -> Command (CTop, rr l)
  | Top -> Top
  | Bottom -> Bottom
  | Abort -> Abort
  | Control -> Control
  | CallCC -> CallCC
  | TypeUnit -> TypeUnit
  | e -> e

let rec find_abort exp =
  match exp with
  | Application (Abort, e) -> Some e
  | Pair (l, r) ->
      let x = find_abort l in
      if Option.is_some x then x else find_abort r
  | Application (l, _) -> find_abort l
  | First x
  | Second x
  | InjectLeft (_, x)
  | InjectRight (_, x)
  | Case (x, _, _)
  | Let (_, x, _) ->
      find_abort x
  | _ -> None

let rec reduce ?(multi = false) ?(nested = true) (e : expr) =
  let rr = reduce ~multi ~nested in
  let isV = is_value ~multi ~nested in
  match e with
  (* | Pair ((Application (Abort, _) as a), _)
  | Pair (_, (Application (Abort, _) as a))
  | InjectLeft (_, (Application (Abort, _) as a))
  | InjectRight (_, (Application (Abort, _) as a))
  | First (Application (Abort, _) as a)
  | Second (Application (Abort, _) as a)
  | LetPair (_, _, (Application (Abort, _) as a), _)
  | Application ((Application (Abort, _) as a), _)
  | Case ((Application (Abort, _) as a), _, _) ->
      a *)
  | Pair (l, r) ->
      let p, l2 = isV l in
      if not (multi || p) then Pair (l2, r) else Pair (l2, rr r)
  | InjectLeft (l, r) -> InjectLeft (l, rr r)
  | InjectRight (l, r) -> InjectRight (l, rr r)
  | First (Pair (l, _)) -> l
  | Second (Pair (_, r)) -> r
  | Lambda (x, b) -> if nested then Lambda (x, rr b) else Lambda (x, b)
  | First e -> First (rr e)
  | Second e -> Second (rr e)
  | Let (x, e, body) ->
      let isV, _ = isV e in
      if nested || isV then body |> substitute x e else Let (x, rr e, body)
  | LetPair (x, y, Pair (l, r), body) ->
      body |> substitute x l |> substitute y r
  | LetPair (x, y, p, body) ->
      let vp, np = isV p in
      if not (multi || vp) then LetPair (x, y, np, body)
      else LetPair (x, y, np, rr body)
  | Application (Lambda (arg, body), r) -> substitute arg r body
  | Application (Mu (arg, body), r) -> substituteCommand arg r body
  | Application (l, r) ->
      let p, l2 = isV l in
      if not (multi || p) then Application (l2, r) else Application (l2, rr r)
  | Case (InjectLeft (_, l), (arg, body), _) -> substitute arg l body
  | Case (InjectRight (_, r), _, (arg, body)) -> substitute arg r body
  | Case (c, ((argL, l) as ll), ((argR, r) as rightCase)) ->
      let cv, cp = isV c in
      if not ((multi || cv) && nested) then Case (cp, ll, rightCase)
      else
        let lv, lp = isV l in
        if not (multi || lv) then Case (cp, (argL, lp), rightCase)
        else Case (cp, (argL, lp), (argR, rr r))
  | Command (CVar arg, Mu (old, b)) -> substitute old (Name arg) b
  | Command (c, m) ->
      Command (c, rr m)
      (* | EvaluationContext (c, Application (CallCC, m)) -> (
      match is_value m with
      | true, _ ->
          let x = find_unique_var m in
          EvaluationContext
            (c, m @- (x /-> (Abort @- EvaluationContext (c, Name x))))
      | false, r -> EvaluationContext (c, Application (CallCC, r)))
  | EvaluationContext (c, Application (Control, m)) -> (
      match is_value m with
      | true, _ ->
          let x = find_unique_var m in
          m @- (x /-> (Abort @- EvaluationContext (c, Name x)))
      | false, r -> EvaluationContext (c, Application (Control, r)))
  | EvaluationContext (c, Application (Abort, m)) -> (
      match is_value m with
      | true, _ -> m
      | false, r -> EvaluationContext (c, Application (Abort, r)))
  | EvaluationContext (a, e) -> EvaluationContext (a, rr e) *)
  | x -> x

and is_value ?(multi = false) ?(nested = true) e =
  let r = reduce ~multi ~nested e in
  (Equality.expr_eq_b e r, r)

let rec isNeutral exp =
  match exp with
  | Name _ -> true
  | First r | Second r -> isNeutral r
  | Application (r, n) -> isNeutral r && isNormal n
  | Case (r, (_, m), (_, n)) -> isNeutral r && isNormal m && isNormal n
  | _ -> false

and isNormal exp =
  match exp with
  | Top | Bottom | Hole | TypeUnit | Abort | CallCC | Control -> true
  | Lambda (_, m) | InjectLeft (_, m) | InjectRight (_, m) -> isNormal m
  | Pair (m, n) -> isNormal m && isNormal n
  | Let (_, r, n) -> isNeutral r && isNormal n
  | LetPair (_, _, r, n) -> isNeutral r && isNormal n
  | r -> isNeutral r

let isAtomic exp =
  match exp with
  | Top | Bottom | Hole | TypeUnit | Abort | CallCC | Control | Name _ -> true
  | _ -> false

let rec isBasic exp =
  match exp with
  | Pair (m, n) -> isAtomic m && isAtomic n
  | InjectLeft (_, m) | InjectRight (_, m) -> isAtomic m
  | Application (r, n) -> isAtomic r && isAtomic n
  | First r | Second r -> isBasic r
  | Let (_, r, n) -> isBasic r && isBasic n
  | _ -> isAtomic exp

let rec isLinear exp =
  match exp with
  | Top | Bottom | Hole | TypeUnit | Abort | CallCC | Control | Name _ -> true
  | Lambda (_, m) -> isLinear m
  | InjectLeft (_, m) | InjectRight (_, m) -> isAtomic m
  | Pair (m, n) -> isAtomic m && isAtomic n
  | First r | Second r -> isAtomic r
  | Application (r, n) -> isAtomic r && isAtomic n
  | Let (_, Let _, _) -> false
  | Let (_, r, n) -> isNormal r && isLinear n
  | LetPair (_, _, r, n) -> isNormal r && isLinear n
  | Case (r, (_, m), (_, n)) -> isNormal r && isBasic m && isBasic n
  | _ -> false

let rec linearize ?(used = StringSet.empty) exp =
  if isLinear exp then exp
  else
    match exp with
    | Top | Bottom | Hole | TypeUnit | Abort | CallCC | Control | Name _ -> exp
    | Lambda (x, n) -> Lambda (x, linearize ~used n)
    | InjectLeft (t, m) ->
        let new_var = find_unique_var ~used exp in
        Let
          ( new_var,
            linearize ~used:(StringSet.add new_var used) m,
            InjectLeft (t, Name new_var) )
    | InjectRight (t, m) ->
        let new_var = find_unique_var ~used exp in
        Let
          ( new_var,
            linearize ~used:(StringSet.add new_var used) m,
            InjectRight (t, Name new_var) )
    | Pair (m, n) ->
        let new_var = find_unique_var ~used exp in
        if not (isAtomic m) then
          Let
            ( new_var,
              linearize ~used:(StringSet.add new_var used) m,
              linearize
                ~used:(StringSet.add new_var used)
                (Pair (Name new_var, n)) )
        else
          Let
            ( new_var,
              linearize ~used:(StringSet.add new_var used) n,
              Pair (m, Name new_var) )
    | Application (m, n) ->
        let new_var = find_unique_var ~used exp in
        if not (isAtomic m) then
          Let
            ( new_var,
              linearize ~used:(StringSet.add new_var used) m,
              linearize
                ~used:(StringSet.add new_var used)
                (Application (Name new_var, n)) )
        else
          Let
            ( new_var,
              linearize ~used:(StringSet.add new_var used) n,
              Application (m, Name new_var) )
    | First r ->
        let new_var = find_unique_var ~used exp in
        Let
          ( new_var,
            linearize ~used:(StringSet.add new_var used) r,
            First (Name new_var) )
    | Second r ->
        let new_var = find_unique_var ~used exp in
        Let
          ( new_var,
            linearize ~used:(StringSet.add new_var used) r,
            Second (Name new_var) )
    | Let (x, Let (y, m, b1), b2) ->
        linearize ~used (Let (y, m, Let (x, b1, b2)))
    | Let (x, m, b) ->
        Let (x, linearize ~used m, linearize ~used:(StringSet.add x used) b)
    | LetPair (x, y, m, b) ->
        linearize ~used (Let (x, First m, Let (y, Second m, b)))
    | Case (m, (x, b), (y, c)) ->
        let new_var = find_unique_var ~used exp in
        if not (isAtomic m) then
          Let
            ( new_var,
              linearize ~used:(StringSet.add new_var used) m,
              linearize
                ~used:(StringSet.add new_var used)
                (Case (Name new_var, (x, linearize b), (y, linearize c))) )
        else if not (isAtomic b) then
          Let
            ( new_var,
              Lambda (x, linearize ~used:(StringSet.add new_var used) b),
              linearize
                ~used:(StringSet.add new_var used)
                (Case (m, (x, Application (Name new_var, Name x)), (y, c))) )
        else if not (isAtomic c) then
          Let
            ( new_var,
              Lambda (y, linearize ~used:(StringSet.add new_var used) c),
              linearize
                ~used:(StringSet.add new_var used)
                (Case (m, (x, b), (y, Application (Name new_var, Name y)))) )
        else Case (m, (x, b), (y, c))
    | x -> failwith (PrettyPrinter.pp_expr x)

let rec useContinuation exp =
  match exp with
  | Lambda (x, b) -> Lambda (x, Lambda ("Cont", useContinuation b))
  | Let (res, Application (f, b), rest) ->
      let continuation = Lambda (res, useContinuation rest) in
      Application (Application (f, b), continuation)
  | Let (x, y, b) -> Let (x, y, useContinuation b)
  | _ -> exp

let rec useControl exp =
  match exp with
  | Lambda (x, b) -> Lambda (x, Lambda ("Cont", useControl b))
  | Let (res, Application (f, b), rest) ->
      let continuation = Lambda (res, useControl rest) in
      Application (Application (f, b), continuation)
  | Let (x, y, b) -> Let (x, y, useControl b)
  | _ -> exp

let rec findControl cmd new_var = function
  | Name x -> (None, Name x)
  | Top -> (None, Top)
  | Bottom -> (None, Bottom)
  | Abort -> (None, Abort)
  | Lambda _ as e -> (None, e)
  | Application (l, r) ->
      if l = cmd then (Some r, Name new_var)
      else
        let c, l2 = findControl cmd new_var l in
        if Option.is_some c then (c, Application (l2, r))
        else
          let c, r2 = findControl cmd new_var r in
          (c, Application (l, r2))
  | Pair (l, r) ->
      let c, l2 = findControl cmd new_var l in
      if Option.is_some c then (c, Pair (l2, r))
      else
        let c, r2 = findControl cmd new_var r in
        (c, Pair (l, r2))
  | First e ->
      let c, e2 = findControl cmd new_var e in
      (c, First e2)
  | Second e ->
      let c, e2 = findControl cmd new_var e in
      (c, Second e2)
  | InjectLeft (t, e) ->
      let c, e2 = findControl cmd new_var e in
      (c, InjectLeft (t, e2))
  | InjectRight (t, e) ->
      let c, e2 = findControl cmd new_var e in
      (c, InjectRight (t, e2))
  | Case (e, l, r) ->
      let c, e2 = findControl cmd new_var e in
      (c, Case (e2, l, r))
  | Let (x, e, b) ->
      let c, r2 = findControl cmd new_var e in
      (c, Let (x, r2, b))
  | e -> failwith ("Missed: " ^ PrettyPrinter.pp_expr e)

let rec expandControl ?(withAbort = true) exp =
  let con_var = find_unique_var ~varset:char_vars2 exp in
  match findControl Control con_var exp with
  | Some v, e ->
      Application
        (v, Lambda (con_var, if withAbort then Application (Abort, e) else e))
  | None, e -> (
      match e with
      | Name x -> Name x
      | Top -> Top
      | Bottom -> Bottom
      | Abort -> Abort
      | Control -> Control
      | CallCC -> CallCC
      | Lambda (x, b) -> Lambda (x, b)
      | Pair (l, r) ->
          Pair (expandControl ~withAbort l, expandControl ~withAbort r)
      | Application (l, r) ->
          Application (expandControl ~withAbort l, expandControl ~withAbort r)
      | First e -> First (expandControl ~withAbort e)
      | Second e -> Second (expandControl ~withAbort e)
      | InjectLeft (t, e) -> InjectLeft (t, expandControl ~withAbort e)
      | InjectRight (t, e) -> InjectRight (t, expandControl ~withAbort e)
      | Let (x, e, b) -> Let (x, expandControl ~withAbort e, b)
      | Case (e, (lx, le), (rx, re)) ->
          Case (expandControl ~withAbort e, (lx, le), (rx, re))
      | e -> failwith ("Missed: " ^ PrettyPrinter.pp_expr e))

let rec expandCC ?(withAbort = true) exp =
  let con_var = find_unique_var ~varset:char_vars2 exp in
  match findControl CallCC con_var exp with
  | Some v, e ->
      let inner =
        Application
          (v, Lambda (con_var, if withAbort then Application (Abort, e) else e))
      in
      substitute con_var inner e
  | None, e -> (
      match e with
      | Name x -> Name x
      | Top -> Top
      | Bottom -> Bottom
      | Abort -> Abort
      | Lambda (x, b) -> Lambda (x, expandCC ~withAbort b)
      | Pair (l, r) -> Pair (expandCC ~withAbort l, expandCC ~withAbort r)
      | Application (l, r) ->
          Application (expandCC ~withAbort l, expandCC ~withAbort r)
      | First e -> First (expandCC ~withAbort e)
      | Second e -> Second (expandCC ~withAbort e)
      | InjectLeft (t, e) -> InjectLeft (t, expandCC ~withAbort e)
      | InjectRight (t, e) -> InjectRight (t, expandCC ~withAbort e)
      | Let (x, e, b) -> Let (x, expandControl ~withAbort e, b)
      | Case (e, (lx, le), (rx, re)) ->
          Case
            ( expandCC ~withAbort e,
              (lx, expandCC ~withAbort le),
              (rx, expandCC ~withAbort re) )
      | e -> failwith ("Missed: " ^ PrettyPrinter.pp_expr e))
