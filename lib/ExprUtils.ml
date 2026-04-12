open Structs

let expr_bin_judge_combine (ee : expr -> expr -> expr)
    (jj : judgement -> judgement -> judgement) =
  let combined { exp = le; judge = lj } { exp = re; judge = rj } =
    { exp = ee le re; judge = jj lj rj }
  in
  combined

let expr_uni_judge_combine (ee : expr -> expr) (jj : judgement -> judgement) =
  let combined { exp = le; judge = lj } = { exp = ee le; judge = jj lj } in
  combined

let forward (l : judgement) (r : judgement) =
  if l == r then l else failwith "Incompaitble judgements"

let wrap_type_combination2 (tf : ty -> ty -> ty) =
  let res (j1 : judgement) (j2 : judgement) =
    match (j1, j2) with
    | TypeOf a, TypeOf b -> TypeOf (tf a b)
    | _ -> failwith "Incompaitble judgements"
  in
  res

let wrap_type_combination1 (tf : ty -> ty) =
  let res (j1 : judgement) =
    match j1 with
    | TypeOf a -> TypeOf (tf a)
    | _ -> failwith "Incompaitble judgements"
  in
  res

let extractLeft (t : ty) =
  match t with
  | Sum (a, _) | Prod (a, _) | Func (a, _) -> a
  | _ -> failwith "Incomaptible Type for ExtractLeft"

let extractRight (t : ty) =
  match t with
  | Sum (_, b) | Prod (_, b) | Func (_, b) -> b
  | _ -> failwith "Incomaptible Type for ExtractRight"

module NatDedExp = struct
  let ( &- ) (l : expr) (r : expr) = And (l, r)
  let ( |- ) (l : expr) (r : expr) = Or (l, r)
  let ( /&- ) (l : expr) (r : expr) = NAnd (l, r)
  let ( /|- ) (l : expr) (r : expr) = Nor (l, r)
  let ( =>- ) (l : expr) (r : expr) = Impl (l, r)
  let ( ~>- ) (l : expr) = Impl (l, Bottom)
  let ( !- ) (l : expr) = Not l
  let all_ x t e = ForAll (x, t, e)
  let exists_ x t e = Exists (x, t, e)
  let ( & ) = expr_bin_judge_combine ( &- ) forward
  let ( /& ) = expr_bin_judge_combine ( /&- ) forward
  let ( || ) = expr_bin_judge_combine ( |- ) forward
  let ( /| ) = expr_bin_judge_combine ( /|- ) forward
  let ( => ) = expr_bin_judge_combine ( =>- ) forward
  let ( ~> ) = expr_uni_judge_combine ( ~>- ) Fun.id
  let ( ! ) = expr_uni_judge_combine ( !- ) Fun.id
  let all x t = expr_uni_judge_combine (all_ x t) Fun.id
  let exists x t = expr_uni_judge_combine (exists_ x t) Fun.id
end

module CurryExpr = struct
  let extractLeft (t : ty) =
    match t with
    | Sum (a, _) | Prod (a, _) | Func (a, _) -> a
    | _ -> failwith "Incomaptible Type for ExtractLeft"

  let extractRight (t : ty) =
    match t with
    | Sum (_, b) | Prod (_, b) | Func (_, b) -> b
    | _ -> failwith "Incomaptible Type for ExtractRight"

  let ( &- ) (l : expr) (r : expr) = Pair (l, r)
  let ( ?<- ) (l : expr) = First l
  let ( ?>- ) (l : expr) = Second l
  let ( /-> ) x body = Lambda (x, body)
  let ( $-> ) x body = Mu (x, body)
  let ( @- ) l r = Application (l, r)

  (* let abort x = Application (Abort, x) *)
  let let_pair x y p b = LetPair (x, y, p, b)
  let let_ x p b = Let (x, p, b)
  let case m ln lb rn rb = Case (m, (ln, lb), (rn, rb))
  let ( * ) (l : ty) (r : ty) = Prod (l, r)
  let ( => ) (l : ty) (r : ty) = Func (l, r)
  let ( + ) (l : ty) (r : ty) = Sum (l, r)
  let ( ! ) (e : ty) = e => BottomType
  let top_ = TypeUnit
  let ( & ) = expr_bin_judge_combine ( &- ) (wrap_type_combination2 ( * ))
  let left ?(t = NoType) e = InjectLeft (t, e)
  let right ?(t = NoType) e = InjectRight (t, e)
  let ( #! ) a b = Command (CVar a, b)
  let ( !% ) b = Command (CTop, b)

  let ( ?< ) =
    expr_uni_judge_combine ( ?<- ) (wrap_type_combination1 extractLeft)

  let ( ?> ) =
    expr_uni_judge_combine ( ?>- ) (wrap_type_combination1 extractRight)

  let top = Utils.is_type top_ UnitType

  let lam (var : string) (t : ty) =
    expr_uni_judge_combine
      (fun a -> Lambda (var, a))
      (wrap_type_combination1 (( => ) t))

  let mu var s =
    match s with
    | { exp = e; judge = ContextType c } ->
        let t = ContextUtils.Context.getType var c in
        { exp = Mu (var, e); judge = t }
    | _ -> failwith "Invalid use of Mu"

  let cmd ctx cvar { exp = m; judge = t } =
    let t2 =
      match cvar with
      | CVar var -> ContextUtils.Context.getType var ctx
      | CTop -> TypeOf BottomType
    in
    if not (Equality.judgement_eq_b t t2) then
      failwith "Type in context must match"
    else { exp = Command (cvar, m); judge = ContextType ctx }

  let ( /=> ) a b = lam (fst a) (snd a) b
  let ( $=> ) = mu

  let ( @ ) l r =
    match (l, r) with
    | { exp = l; judge = TypeOf (Func (_, b1)) }, { exp = r; judge = TypeOf _ }
      ->
        { exp = l @- r; judge = TypeOf b1 }
    | _ -> failwith "Left Side is not Function Type"

  let injL t =
    expr_uni_judge_combine
      (fun a -> InjectLeft (t, a))
      (wrap_type_combination1 (fun l -> l + t))

  let injR t =
    expr_uni_judge_combine
      (fun a -> InjectRight (t, a))
      (wrap_type_combination1 (( + ) t))

  let caseStmt m a na b nb =
    let tp =
      match (na, nb) with
      | { exp = _; judge = TypeOf c }, { exp = _; judge = TypeOf c2 } ->
          if Equality.type_eq_b c c2 then c else failwith "Incompatible Types"
      | _ -> failwith "Incompatible Types"
    in
    match (m, na, nb) with
    | ( { exp = mE; judge = _ },
        { exp = naE; judge = _ },
        { exp = nbE; judge = _ } ) ->
        { exp = Case (mE, (a, naE), (b, nbE)); judge = TypeOf tp }

  (* let abortTyped x y = { exp = Application (Abort, x); judge = TypeOf y } *)
end

module ModalExp = struct
  include NatDedExp

  let ( !!- ) (l : expr) = Box (NoContext, l, NoJudge)
  let ( !! ) = expr_uni_judge_combine ( !!- ) Fun.id
  let ( |-> ) (c : context) (s : expr) = Box (c, s, NoJudge)
  let ( ||-> ) (c : context) (s : expr) = Box (c, s, Valid)

  let ( |=> ) (c : context) (s : stmt) =
    { exp = Box (c, s.exp, s.judge); judge = s.judge }

  let ( ||=> ) (c : context) (s : stmt) =
    { exp = Box (c, s.exp, Valid); judge = s.judge }
end

module TemporalExp = struct
  include NatDedExp

  let ( !!- ) (l : expr) = NextTime l
  let ( !! ) = expr_uni_judge_combine ( !!- ) Fun.id
end

module LinearExp = struct
  let ( &- ) (l : expr) (r : expr) = LinAndSum (l, r)
  let ( *- ) (l : expr) (r : expr) = LinAndProd (l, r)
  let ( |- ) (l : expr) (r : expr) = LinOrSum (l, r)
  let ( +- ) (l : expr) (r : expr) = LinOrProd (l, r)
  let ( =>- ) (l : expr) (r : expr) = LinImpl (l, r)
  let ( !- ) (l : expr) = Bang l
  let ( & ) = expr_bin_judge_combine ( &- ) forward
  let ( * ) = expr_bin_judge_combine ( *- ) forward
  let ( || ) = expr_bin_judge_combine ( |- ) forward
  let ( + ) = expr_bin_judge_combine ( +- ) forward
  let ( => ) = expr_bin_judge_combine ( =>- ) forward
  let ( ! ) = expr_uni_judge_combine ( !- ) Fun.id
end
