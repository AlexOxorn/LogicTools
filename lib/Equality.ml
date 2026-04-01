open Structs

let rec type_eq_b (l: ty) (r: ty) = match (l, r) with
| UnitType, UnitType -> true
| NoType, NoType -> true
| (NamedType l), (NamedType r) -> l = r
| (Sum (ll, lr)), (Sum (rl, rr))
| (Prod (ll, lr)), (Prod (rl, rr))
| (Func (ll, lr)), (Func (rl, rr)) -> (type_eq_b ll rl) && (type_eq_b lr rr)
| _ -> false
and expr_eq_b (l: expr) (r: expr) = match (l, r) with
| Top, Top
| Bottom, Bottom -> true
| LinOne, LinOne -> true
| LinZero, LinZero -> true
| Abort, Abort -> true
| Control, Control -> true
| CallCC, CallCC -> true
| (Name a), (Name b) -> a = b
| (And (ll, lr)), (And (rl, rr))
| (NAnd (ll, lr)), (NAnd (rl, rr))
| (Or (ll, lr)), (Or (rl, rr))
| (Pair(ll, lr), (Pair(rl, rr)))
| (Application(ll, lr), (Application(rl, rr)))
| (LinAndSum (ll, lr)), (LinAndSum (rl, rr))
| (LinAndProd (ll, lr)), (LinAndProd (rl, rr))
| (LinImpl (ll, lr)), (LinImpl (rl, rr))
| (LinOrSum (ll, lr)), (LinOrSum (rl, rr))
| (LinOrProd (ll, lr)), (LinOrProd (rl, rr))
| (EvaluationContext ((ll, _), (lr, _))), (EvaluationContext ((rl, _),(rr, _)))
| (Impl (ll, lr)), (Impl (rl, rr)) -> (expr_eq_b ll rl) && (expr_eq_b lr rr) 
| (Not l), (Not r) -> expr_eq_b l r
| (Bang l), (Bang r) -> expr_eq_b l r
| (First l), (First r) -> expr_eq_b l r
| (Second l), (Second r) -> expr_eq_b l r
| Lambda (lx, lb), Lambda (rx, rb) -> lx = rx && (expr_eq_b lb rb)
| (InjectRight (tl, el)), (InjectRight (tr, er))
| (InjectLeft (tl, el)), (InjectLeft (tr, er)) -> (type_eq_b tl tr) && (expr_eq_b el er)
| (Box (c1, s1, j1)), (Box (c2, s2, j2)) -> (context_strict_equal_b c1 c2) && (expr_eq_b s1 s2) && (judgement_eq_b j1 j2)
| (Predicate (n1, exps1)), (Predicate (n2, _)) -> (n1 = n2)  && (List.for_all2 expr_eq_b exps1 exps1)
| (ForAll (n1, ty1, e1)), (ForAll (n2, ty2, e2)) -> (n1 = n2) && (type_eq_b ty1 ty2) && (expr_eq_b e1 e2)
| (Exists (n1, ty1, e1)), (Exists (n2, ty2, e2)) -> (n1 = n2) && (type_eq_b ty1 ty2) && (expr_eq_b e1 e2)
| _ -> (*(Printf.eprintf "Unsupported Expression For Equality\n%s\n%s\n" (PrettyPrinter.pp_expr l) (PrettyPrinter.pp_expr r));*)
false
and judgement_eq_b (l: judgement) (r: judgement) = match (l, r) with
| NoJudge, NoJudge
| Truth, Truth
| Valid, Valid -> true
| _ -> Printf.eprintf "Unsupported Judgement\n"; false
and stmt_eq_b {exp=e1; judge=j1} {exp=e2; judge=j2} = (expr_eq_b e1 e2) && (judgement_eq_b j1 j2)
and assumption_eq_b (l: assumption) (r: assumption) = match (l, r) with
| (StmtAssumption (n1, s1)), (StmtAssumption (n2, s2)) -> (n1 = n2) && (stmt_eq_b s1 s2)
| (VariableAssumption (n1, (TypeOf t1))), (VariableAssumption (n2, (TypeOf t2))) -> (n1 = n2) && (type_eq_b t1 t2)
| _ -> false
and context_strict_equal_b (l: context) (r: context) = match l, r with
| (ConName a), (ConName b) -> a = b
| (ConApp (c1, a1)), (ConApp (c2, a2)) -> (assumption_eq_b a1 a2) && (context_strict_equal_b c1 c2)
| (ConCat (c1, a1)), (ConCat (c2, a2)) -> (context_strict_equal_b a1 a2) && (context_strict_equal_b c1 c2)
| (ConNameWithDef (n1, c1)), (ConNameWithDef (n2, c2)) -> n1 == n2 && (context_strict_equal_b c1 c2)
| Empty, Empty
| NoContext, NoContext -> true
| (ConNameWithDef (_, c1)), x
| x, (ConNameWithDef (_, c1)) -> (context_strict_equal_b c1 x)
| _ -> false

let rec assumption_in_context_b (s: assumption) (c: context) = match c with 
| ConCat (c1, c2) -> (assumption_in_context_b s c2) || (assumption_in_context_b s c1)
| ConApp (c1, a)  -> (assumption_eq_b s a) || (assumption_in_context_b s c1)
| ConNameWithDef (_, c1)  -> (assumption_in_context_b s c1)
| _ -> false;;

let judge_eq_b (l: judgement) (r: judgement) = match l, r with
| Truth, Truth
| NoJudge, NoJudge -> true
| (TypeOf t1), (TypeOf t2) -> type_eq_b t1 t2
| _ -> false