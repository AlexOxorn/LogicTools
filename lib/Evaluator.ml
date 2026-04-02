open Structs

let stmt_to_exp_ty = function
  | { exp = e; judge = TypeOf t } -> (e, t)
  | _ -> failwith "UnTyped"

let vars = List.init 26 (fun i -> Char.escaped (Char.chr (int_of_char 'a' + i)))

let multi_char_vars =
  Seq.(
    append (List.to_seq vars)
      (concat
         (List.to_seq vars
         |> map (fun c -> map (fun x -> c ^ x) (List.to_seq vars)))))

module StringSet = Set.Make (String)

let rec collect_vars = function
  | Name x -> StringSet.singleton x
  | Pair (l, r) | Application (l, r) | EvaluationContext ((l, _), (r, _)) ->
      StringSet.union (collect_vars l) (collect_vars r)
  | InjectLeft (_, e) | InjectRight (_, e) | First e | Second e ->
      collect_vars e
  | Case (c, (argL, l), (argR, r)) ->
      StringSet.(
        collect_vars c
        |> union (singleton argL)
        |> union (collect_vars l)
        |> union (singleton argR)
        |> union (collect_vars r))
  | _ -> StringSet.empty

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
  | EvaluationContext ((e, t), (v, t2)) ->
      EvaluationContext ((rr e, t), (rr v, t2))
  | Top -> Top
  | Bottom -> Bottom
  | Abort -> Abort
  | Control -> Control
  | CallCC -> CallCC
  | TypeUnit -> TypeUnit
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

let find_unique_var e =
  let names = collect_vars e in
  Option.value ~default:"\\_\\_x"
    (Seq.find (fun x -> not (StringSet.mem x names)) multi_char_vars)

let rec reduce ?(multi=false) (e : expr) =
  let open ExprUtils.CurryExpr in
  Printf.eprintf "%s\n--------------------------\n"
    (PrettyPrinter.literal_expr e);
  match e with
  | Pair(Application(Abort, _) as a, _)
  | Pair(_, (Application(Abort, _) as a))
  | InjectLeft (_, (Application(Abort, _) as a))
  | InjectRight (_, (Application(Abort, _) as a))
  | First (Application(Abort, _) as a)
  | Second (Application(Abort, _) as a) 
  | LetPair (_, _, (Application(Abort, _) as a), _)
  | Application((Application(Abort, _) as a), _)
  | Case ((Application(Abort, _) as a), _, _)
    -> a
  | Pair (l, r) ->
      let p, l2 = is_value l in
      if not (multi || p) then Pair (l2, r) else Pair (l2, reduce ~multi r)
  | InjectLeft (l, r) -> InjectLeft (l, reduce ~multi r)
  | InjectRight (l, r) -> InjectRight (l, reduce ~multi r)
  | First (Pair (l, _)) -> l
  | Second (Pair (_, r)) -> r
  | Lambda (x, b) -> Lambda (x, reduce ~multi b)
  | First e -> First (reduce ~multi e)
  | Second e -> Second (reduce ~multi e)
  | LetPair (x, y, Pair (l, r), body) ->
      (body |> substitute x l |> substitute y r)
  | LetPair (x, y, p, body) ->
      let vp, np = is_value p in
      if not (multi || vp) then LetPair (x, y, np, body) else LetPair (x, y, np, reduce ~multi body)
  | Application (Lambda (arg, body), r) -> substitute arg r body
  | Application (l, r) ->
      let p, l2 = is_value l in
      if not (multi || p) then Application (l2, r) else Application (l2, reduce ~multi r)
  | Case (InjectLeft (_, l), (arg, body), _) -> substitute arg l body
  | Case (InjectRight (_, r), _, (arg, body)) ->
      substitute arg r body
  | Case (c, ((argL, l) as ll), ((argR, r) as rr)) ->
      let cv, cp = is_value c in
      if not (multi || cv) then Case (cp, ll, rr)
      else
        let lv, lp = is_value l in
        if not (multi || lv) then Case (cp, (argL, lp), rr)
        else Case (cp, (argL, lp), (argR, reduce ~multi r))
  | EvaluationContext (((_, et) as c), (Application (CallCC, m), t)) -> (
      match is_value m with
      | true, _ ->
          let x = find_unique_var m in
          EvaluationContext
            (c, (m @- (x /-> (Abort @- EvaluationContext (c, (Name x, t)))), et))
      | false, r -> EvaluationContext (c, (Application (CallCC, r), t)))
  | EvaluationContext (c, (Application (Control, m), t)) -> (
      match is_value m with
      | true, _ ->
          let x = find_unique_var m in
          m @- (x /-> (Abort @- EvaluationContext (c, (Name x, t))))
      | false, r -> EvaluationContext (c, (Application (Control, r), t)))
  | EvaluationContext (c, (Application (Abort, m), t)) -> (
      match is_value m with
      | true, _ -> m
      | false, r -> EvaluationContext (c, (Application (Abort, r), t)))
  | EvaluationContext (a, (e, t)) -> EvaluationContext (a, (reduce ~multi e, t))
  | x -> x

and is_value ?(multi=false) e =
  let r = reduce ~multi e in
  (Equality.expr_eq_b e r, r)
