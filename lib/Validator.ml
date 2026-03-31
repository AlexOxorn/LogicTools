open Structs
open Utils
open ContextUtils

type error_type = ExprNotEqual of expr * expr
                | TypeNotEqual of ty * ty
                | JudgementNotEqual of judgement * judgement
                | StmtNotEqual of stmt * stmt
                | AssumptionNotEqual of assumption * assumption
                | ContextNotEqual of context * context
                | NotInContext of context * assumption
                | TargetNameNotCorrect of string * string
                | AssumptionNotInContext of string * context
                | NoMatchingRule of context * expr * inference * (proof list);;

exception Foo of error_type;;

let wrap_eq_res (error_constructor) (eq_expression) l r =
  if (eq_expression l r) then Ok () else Error (error_constructor l r)

let (&&@) x b = Result.bind x (fun () -> Lazy.force b);;
let (=@) l r = if (l = r) then Ok() else Error (TargetNameNotCorrect (l, r));;



let type_eq = wrap_eq_res (fun x y -> TypeNotEqual (x, y)) Equality.type_eq_b;;
let judge_eq = wrap_eq_res (fun x y -> JudgementNotEqual (x, y)) Equality.judge_eq_b;;
let expr_eq = wrap_eq_res (fun x y -> ExprNotEqual (x, y)) Equality.expr_eq_b;;
let judgement_eq = wrap_eq_res (fun x y -> JudgementNotEqual (x, y)) Equality.judgement_eq_b;;
let stmt_eq = wrap_eq_res (fun x y -> StmtNotEqual (x, y)) Equality.stmt_eq_b;;
let assumption_eq = wrap_eq_res (fun x y -> AssumptionNotEqual (x, y)) Equality.assumption_eq_b;;
let context_strict_equal = wrap_eq_res (fun x y -> ContextNotEqual (x, y)) Equality.context_strict_equal_b;;

let context_equivalent = wrap_eq_res (fun x y -> ContextNotEqual (x, y)) Context.equivalent
let assumption_in_context = wrap_eq_res (fun x y -> NotInContext (y, x)) Equality.assumption_in_context_b;;


let extractDataFromInference ({con=c; term=s; inf=i; _}: proof) = match (s, !i) with
| {exp=e; judge=j}  , (Inference (r, p)) -> (c, e, r, p, j)
| {exp=_; judge=Truth}  , (NoInference)
| {exp=_; judge=Truth}  , (Deduction _) -> (c, Top, Axiom, [], Truth)
| _ -> (c, Bottom, Axiom, [], NoJudge)


let check_flat_correctness (p: proof) = 
  match (extractDataFromInference p) with
    (* TOP LEVEL *)
    | _, Top, Axiom, [], _ -> Ok()
    | c, e, (Assumption a), [], NoJudge ->  assumption_in_context (StmtAssumption (a, (no_judge e))) c
    | c, e, (Assumption a), [], Truth ->  assumption_in_context (StmtAssumption (a, (is_true e))) c
    | c, e, (ValidAssumption a), [], Truth ->  assumption_in_context (StmtAssumption (a, (is_valid e))) c
    | c, _, (Assumption a), [], (TypeOf t) -> assumption_in_context (VariableAssumption (a, (TypeOf t))) c
    (* AND INTRO *)
    | c, And(l, r), (AndIntro), [l_proof; r_proof], Truth -> (expr_eq l_proof.term.exp l) &&@
                                                      lazy (expr_eq r_proof.term.exp r) &&@
                                                      lazy (context_strict_equal c l_proof.con) &&@
                                                      lazy (context_strict_equal c r_proof.con)
    (* BASIC BINARIES AndE OrI *)
    | c, e, (AndElimLeft), [{con=c1; term={exp=And(sube, _);_}; _}], Truth 
    | c, e, (AndElimRight), [{con=c1; term={exp=And(_, sube);_}; _}] , Truth 
    | c, (Or(e, _)), (OrIntroLeft), [{con=c1; term={exp=sube; _}; _}], Truth 
    | c, (Or(_, e)), (OrIntroRight), [{con=c1; term={exp=sube; _}; _}], Truth        -> (context_strict_equal c c1) &&@ lazy(expr_eq sube e)
    (* OR ELINIMATION *)
    | c, e, (OrElim (x, y)), [
      {con=c1; term={exp=Or(l, r); _};_};
      {con=cl; term={exp=e2; _};_};
      {con=cr; term={exp=e3; _};_};
    ], Truth  -> (expr_eq e e2) &&@
         lazy (expr_eq e e3) &&@
         lazy (context_strict_equal c c1) &&@
         lazy (context_strict_equal (ConApp(c, StmtAssumption(x, is_true l))) cl) &&@
         lazy (context_strict_equal (ConApp(c, StmtAssumption(y, is_true r))) cr)
    (* IMPLICATION *)
    | c, (Impl (pre, post)), (ImplIntro name), [{con=c1; term={exp=post1;_};_}], Truth  -> (
            match Context.lookupStmt name c1 with
            | None -> Error (AssumptionNotInContext(name, c1))
            | Some stmt ->
            (expr_eq post post1) &&@
            lazy (stmt_eq stmt (is_true pre)) &&@
            lazy (context_equivalent c (Context.remove_name name c1)))
    | c, post, (ImplElim), [
      {con=c1; term={exp=Impl(pre1, post1); _};_};
      {con=c2; term={exp=pre2; _};_};
    ], Truth  -> (expr_eq post post1) &&@
         lazy (expr_eq pre1 pre2) &&@
         lazy (context_strict_equal c c1) &&@
         lazy (context_strict_equal c c2)
    (* NOT *)
    | c, (Not e), (NotIntro (targetname, varname)), [{con=c1; term={exp=Name(tmpname);_};_}], Truth  ->
         (targetname =@ tmpname) &&@
         lazy (context_strict_equal (ConApp(c, (StmtAssumption(varname, is_true e)))) c1)
    | c, _, (NotElim), [
      {con=c1; term={exp=Not(a); _};_};
      {con=c2; term={exp=b; _};_};
    ], Truth  ->  (expr_eq a b) &&@
          lazy (context_strict_equal c c1) &&@
          lazy (context_strict_equal c c2)
    | c, e, (ByContra (targetname, varname)), [{con=c1; term={exp=Name(tmpname);_};_}], Truth  ->
        (targetname =@ tmpname) &&@
        lazy (context_strict_equal (ConApp(c, StmtAssumption(varname, is_true (Not e)))) c1)
    (* Custom Nand *)
    | c, NAnd(l, r), (NAndIntro (targetname, lname, rname)), [{con=c1; term={exp=Name(tmpname);_};_}], Truth  ->
      (targetname =@ tmpname) &&@
      lazy (context_strict_equal 
        (ConApp((ConApp(c, (StmtAssumption(lname, is_true l)))), (StmtAssumption(rname, is_true r)))) c1)
    | c, (Name _), (NAndElim), [
      {con=c1; term={exp=NAnd(a, b); _};_};
      {con=c2; term={exp=a1; _};_};
      {con=c3; term={exp=b1; _};_};
    ], Truth  ->  (expr_eq a a1) &&@
          lazy (expr_eq b b1) &&@
          lazy (context_strict_equal c c1) &&@
          lazy (context_strict_equal c c2) &&@
          lazy (context_strict_equal c c3)
    (* Forall / Existence *)
    | c, (Exists(n, ty, e)), (ExistsIntro), [
      {con=c2; term={exp=e2; judge=(TypeOf ty2)};_};
      {con=c1; term={exp=e1; _};_};
    ], Truth  ->  (type_eq ty ty2) &&@
          lazy (expr_eq (Translator.substitue n e2 e) e1) &&@
          lazy (context_strict_equal c c1) &&@
          lazy (context_strict_equal c c2)
    | c, (res), (ExistsElim(var, sub)), [
            {con=c1; term={exp=Exists(n1, ty, ex); _};_};
            {con=c2; term={exp=res2; judge=_};_};
          ], Truth  ->  
            let subcontext = ConApp(ConApp(c, 
                VariableAssumption(var, (TypeOf ty))),
                StmtAssumption(sub, is_true(Translator.substitue n1 (Name var) ex))) in
            (expr_eq res res2) &&@
            (* lazy (judge_eq j1 j2) &&@ *)
            lazy (context_strict_equal c c1) &&@
            lazy (context_strict_equal subcontext c2)
    | c, (res), (ForAllElim), [
            {con=c2; term={exp=e2; judge=(TypeOf ty2)};_};
            {con=c1; term={exp=ForAll(n, ty1, allexp); _};_};
          ], Truth  ->
            (expr_eq res (Translator.substitue n e2 allexp)) &&@
            lazy (type_eq ty1 ty2) &&@
            lazy (context_strict_equal c c1) &&@
            lazy (context_strict_equal c c2)
    | c, (ForAll(n, ty, e)), (ForAllIntro a), [
            {con=c1; term={exp=e1; _};_};
          ], Truth  ->
            let subcontext = ConApp(c, 
                VariableAssumption(a, (TypeOf ty)))
            in
            (expr_eq (Translator.substitue n (Name a) e) e1) &&@
            lazy (context_strict_equal subcontext c1)
    | c, e, j, p, _ -> Error (NoMatchingRule (c, e, j, p))


let rec check_above_proofs (p: proof) = 
  match (!(p.inf)) with
  | Inference (_, subproofs) -> (List.to_seq subproofs) |> Seq.map (fun a -> lazy (check_truth_correctness a)) |> Seq.fold_left (&&@) (Ok())
  | _ -> Ok()
and check_truth_correctness (p: proof) : (unit, error_type) result = 
  (check_flat_correctness p) &&@ lazy (check_above_proofs p)