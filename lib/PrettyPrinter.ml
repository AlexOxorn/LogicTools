open Structs

let repeat_tailrec s n =
  let rec helper acc count =
    if count <= 0 then acc else helper (acc ^ s) (count - 1)
  in
  helper "" n

let indent = repeat_tailrec "  "

let rec literal_expr ?(i = 1) (e : expr) =
  match e with
  | Name a -> Format.asprintf "Name(%s)" a
  | Top -> "Top"
  | Bottom -> "Bottom"
  | Abort -> "Abort"
  | And (l, r) ->
      Format.asprintf "AND(\n%s%s,\n%s%s)" (indent i)
        (literal_expr ~i:(i + 1) l)
        (indent i)
        (literal_expr ~i:(i + 1) r)
  | NAnd (l, r) ->
      Format.asprintf "NAND(\n%s%s,\n%s%s)" (indent i)
        (literal_expr ~i:(i + 1) l)
        (indent i)
        (literal_expr ~i:(i + 1) r)
  | Or (l, r) ->
      Format.asprintf "OR(\n%s%s,\n%s%s)" (indent i)
        (literal_expr ~i:(i + 1) l)
        (indent i)
        (literal_expr ~i:(i + 1) r)
  | Impl (l, r) ->
      Format.asprintf "IMPL(\n%s%s,\n%s%s)" (indent i)
        (literal_expr ~i:(i + 1) l)
        (indent i)
        (literal_expr ~i:(i + 1) r)
  | Not e -> Format.asprintf "NOT(%s)" (literal_expr ~i:(i + 1) e)
  | TypeUnit -> "()"
  | Pair (l, r) ->
      Format.asprintf "PAIR(\n%s%s,\n%s%s)" (indent i)
        (literal_expr ~i:(i + 1) l)
        (indent i)
        (literal_expr ~i:(i + 1) r)
  | First e -> Format.asprintf "FST(%s)" (literal_expr ~i:(i + 1) e)
  | Second e -> Format.asprintf "SND(%s)" (literal_expr ~i:(i + 1) e)
  | Application (l, r) ->
      Format.asprintf "APP(\n%s%s,\n%s%s)" (indent i)
        (literal_expr ~i:(i + 1) l)
        (indent i)
        (literal_expr ~i:(i + 1) r)
  | Lambda (x, r) ->
      Format.asprintf "LAM(\n%s%s, %s)" (indent i) x (literal_expr ~i:(i + 1) r)
  | InjectLeft (_, r) -> Format.asprintf "INJL(%s)" (literal_expr ~i:(i + 1) r)
  | InjectRight (_, r) -> Format.asprintf "INJR(%s)" (literal_expr ~i:(i + 1) r)
  | LetPair (x, y, p, m) ->
      Format.asprintf "LET_PAIR(\n%s%s,%s,\n%s%s,\n%s%s)" (indent i) x y
        (indent i)
        (literal_expr ~i:(i + 1) p)
        (indent i)
        (literal_expr ~i:(i + 1) m)
  | Case (x, (ln, lb), (rn, rb)) ->
      Format.asprintf "CASE(\n%s%s,\n%s%s, %s,\n%s%s, %s)" (indent i)
        (literal_expr ~i:(i + 1) x)
        (indent i) ln
        (literal_expr ~i:(i + 1) lb)
        (indent i) rn
        (literal_expr ~i:(i + 1) rb)
  | _ -> "not implemented 'literal_expr'"

let rec pp_expr (e : expr) =
  match e with
  | Name a -> Format.asprintf "Name(%s)" a
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
  | Lambda (x, r) -> Format.asprintf "\\lam %s.%s" x (pp_expr r)
  | Mu (x, r) -> Format.asprintf "\\mu %s.%s" x (pp_expr r)
  | Command (CVar x, b) -> Format.asprintf "[%s](%s)" x (pp_expr b)
  | Command (CTop, b) -> Format.asprintf "[\\bot](%s)" (pp_expr b)
  | InjectLeft (_, r) -> Format.asprintf "injL %s" (pp_expr r)
  | InjectRight (_, r) -> Format.asprintf "injR %s" (pp_expr r)
  | Box (c, e, j) ->
      Format.asprintf "[%s %s %s]" (pp_con c) (pp_expr e) (pp_judgement j)
  | LetPair (x, y, p, m) ->
      Format.asprintf "let (%s, %s) = (%s) in (%s)" x y (pp_expr p) (pp_expr m)
  | Let (x, p, m) ->
      Format.asprintf "let %s = (%s) in (%s)" x (pp_expr p) (pp_expr m)
  | Case (x, (ln, lb), (rn, rb)) ->
      Format.asprintf "case (%s) { L(%s) -> %s | R(%s) -> %s}" (pp_expr x) ln
        (pp_expr lb) rn (pp_expr rb)
  | _ -> "not implemented 'pp_expr'"

and pp_type (t : ty) =
  match t with
  | NoType -> "(/)"
  | NamedType x -> Format.asprintf "Name(%s)" x
  | UnitType -> "()"
  | BottomType -> "BottomType"
  (* | NotType l -> Format.asprintf "(!%s)" (pp_type l) *)
  | Sum (l, r) -> Format.asprintf "(%s + %s)" (pp_type l) (pp_type r)
  | Prod (l, r) -> Format.asprintf "(%s * %s)" (pp_type l) (pp_type r)
  | Func (l, r) -> Format.asprintf "(%s -> %s)" (pp_type l) (pp_type r)

and pp_judgement (j : judgement) =
  match j with
  | NoJudge -> "()"
  | Truth -> "true"
  | Up -> "Up"
  | Down -> "Down"
  | Valid -> "Valid"
  | ContextType c -> "(" ^ pp_con c ^ ")"
  | TypeOf t -> Format.asprintf "isType %s" (pp_type t)

and pp_stmt (s : stmt) =
  match s with
  | { exp = e; judge = j } ->
      Format.asprintf "{exp=%s; judge=%s}" (pp_expr e) (pp_judgement j)

and pp_con (c : context) =
  match c with
  | ConName n -> Format.asprintf "C%s" n
  | ConApp (c, StmtAssumption (n, s)) ->
      Format.asprintf "%s,%s:%s" (pp_con c) n (pp_stmt s)
  | ConApp (c, VariableAssumption (n, s)) ->
      Format.asprintf "%s,%s:%s" (pp_con c) n (pp_judgement s)
  | ConCat (c1, c2) -> Format.asprintf "(%s;%s)" (pp_con c1) (pp_con c2)
  | ConNameWithDef (n, c) -> Format.asprintf "(%s|%s)" n (pp_con c)
  | Empty -> "_"
  | NoContext -> "X"
