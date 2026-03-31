open Structs

let rec pp_expr (e: expr) = match e with
| Name a -> Format.asprintf("Name(%s)") a
| Top -> "Top"
| Bottom -> "Bottom"
| And (l, r) -> Format.asprintf "(%s && %s)" (pp_expr l) (pp_expr r)
| NAnd (l, r) -> Format.asprintf "!(%s && %s)" (pp_expr l) (pp_expr r)
| Or (l, r) -> Format.asprintf "(%s || %s)" (pp_expr l) (pp_expr r)
| Impl (l, r) -> Format.asprintf "(%s => %s)" (pp_expr l) (pp_expr r)
| Not e -> Format.asprintf "!%s" (pp_expr e)
| TypeUnit -> "()"
| Pair (l, r) -> Format.asprintf "(%s, %s)" (pp_expr l) (pp_expr r)
| First e -> Format.asprintf "fst %s" (pp_expr e)
| Second e -> Format.asprintf "snd %s" (pp_expr e)
| Application (l, r) -> Format.asprintf "%s(%s)" (pp_expr l) (pp_expr r)
| Lambda (x, r) -> Format.asprintf "\\%s.%s" (x) (pp_expr r)
| InjectLeft (_, r) -> Format.asprintf "injL %s" (pp_expr r)
| InjectRight (_, r) -> Format.asprintf "injL %s" (pp_expr r)
| Box (c, e, j) -> Format.asprintf "[%s %s %s]" (pp_con c) (pp_expr e) (pp_judgement j)
| _ -> "not implemented 'pp_expr'"
and pp_type (t: ty) = match t with
| NoType -> "(/)"
| NamedType x -> Format.asprintf("Name(%s)") x
| UnitType -> "()"
| BottomType -> "BottomType"
| Sum (l, r) -> Format.asprintf "(%s + %s)" (pp_type l) (pp_type r)
| Prod (l, r) -> Format.asprintf "(%s * %s)" (pp_type l) (pp_type r)
| Func (l, r) -> Format.asprintf "(%s -> %s)" (pp_type l) (pp_type r)
and pp_judgement (j: judgement) = match j with
| NoJudge -> "()"
| Truth -> "true"
| Up -> "Up"
| Down -> "Down"
| Valid -> "Valid"
| TypeOf t -> Format.asprintf ("isType %s") (pp_type t)
and pp_stmt (s: stmt) = match s with
| {exp=e; judge=j} -> Format.asprintf "{exp=%s; judge=%s}" (pp_expr e) (pp_judgement j)
and pp_con (c: context) = match c with
| ConName n -> Format.asprintf "C%s" n
| ConApp (c, StmtAssumption(n, s)) -> Format.asprintf("%s,%s:%s") (pp_con c) n (pp_stmt s)
| ConApp (c, VariableAssumption(n, s)) -> Format.asprintf("%s,%s:%s") (pp_con c) n (pp_judgement s)
| ConCat (c1, c2) -> Format.asprintf "(%s;%s)" (pp_con c1) (pp_con c2)
| ConNameWithDef (n, c) -> Format.asprintf("(%s|%s)") n (pp_con c)
| Empty -> "_"
| NoContext -> "X"
