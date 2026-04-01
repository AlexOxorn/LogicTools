open Structs
open Validator
module StringMap = Map.Make(String);;

let wrap_paran test str = match test with
| true -> Format.asprintf("(%s)") str
| false -> str

let precedence = function
  | Name _ | Top | Bottom | TypeUnit | Control | Abort
  | CallCC
  | LinOne | LinZero  -> 0
  | Pair _ -> 1
  | Not _ | Predicate _ | Box _ | Application _
  | First _ | Second _ | NextTime _ | Bang _
  | InjectLeft _ | InjectRight _ 
  | EvaluationContext _
    -> 2
  | And _| NAnd _ | Or _ | Nor _
  | LinAndProd _ | LinAndSum _ 
  | LinOrProd _ | LinOrSum _ -> 4
  | ForAll _ | Exists _ | Lambda _ -> 5
  | Impl _ | Let _ | LinImpl _-> 6
  | CtxExp _ -> 7
  | Case _ -> 8

let type_precedence = function
  | UnitType | BottomType | NoType | NamedType _ -> 0
  | Prod _ | Sum _ -> 1
  | Func _ -> 2

let expr_is_atomic (e: expr) = (precedence e) = 0;;
let type_is_atomic (e: ty) = match e with
| NamedType _ | UnitType | BottomType -> true
| _ -> false


let lt_prec l r = (precedence l) < (precedence r);;
let le_prec l r = (precedence l) <= (precedence r);;
let ty_lt_prec l r = (type_precedence l) < (type_precedence r);;
let ty_le_prec l r = (type_precedence l) <= (type_precedence r);;


let rec expr_latex (e: expr) =
  let rec inner wrap (e: expr) = 
    (let base = match e with
    (* Nat Deduction *)
    | Name x -> x
    | Top -> "\\top"
    | Bottom -> "\\bot"
    | And (l, r) -> Format.asprintf "%s \\land %s" (inner (le_prec e l) l) (inner  (le_prec e r) r)
    | Or (l, r) -> Format.asprintf "%s \\lor %s" (inner (le_prec e l) l) (inner (le_prec e r) r)
    | Impl (l, r) -> Format.asprintf "%s \\supset %s" (inner (le_prec e l) l) (inner (lt_prec e r) r)
    | Not (n) -> Format.asprintf "\\lnot %s" (inner (lt_prec e n) n)
    | NAnd (l, r) -> Format.asprintf "%s \\mathbin{\\overline{\\land}} %s" (inner (le_prec e l) l) (inner (le_prec e r) r)
    | Nor (l, r) -> Format.asprintf "%s \\mathbin{\\overline{\\lor}} %s" (inner (le_prec e l) l) (inner (le_prec e r) r)
    
    (* Curry Howard *)
    | TypeUnit -> "()"
    | Pair (l, r) -> Format.asprintf "\\langle %s, %s \\rangle" (inner false l) (inner false r)
    | First n -> "\\text{fst }" ^ (inner (lt_prec e n) n)
    | Second n -> "\\text{snd }" ^ (inner (lt_prec e n) n)
    | Application (l, r) -> Format.asprintf "%s\\ %s" (inner (lt_prec e l) l) (inner (le_prec e r) r)
    | Lambda (arg, body) -> Format.asprintf "\\lambda %s.%s" (arg) (inner false body)
    | Case (pred, (x1, b1), (x2, b2)) -> 
      Format.asprintf 
        "\\text{Case } %s \\text{ of inj}_l\\ %s \\Rightarrow %s \\ |\\text{ inj}_r\\ %s \\Rightarrow %s"
        (inner false pred) x1 (inner (8 = precedence b1) b1) x2 (inner (8 = precedence b2) b2)
    | InjectLeft (t, n) -> Format.asprintf "\\text{inj}_l^{%s} %s" (type_latex t) (inner (lt_prec e n) n)
    | InjectRight (t, n) -> Format.asprintf "\\text{inj}_r^{%s} %s" (type_latex t) (inner (lt_prec e n) n)
    
    (* First Order *)
    | Predicate (n, e) -> Format.asprintf "%s(%s)" (n) (e |> List.map (inner false) |> String.concat ", ")
    | ForAll (n, NoType, e) -> Format.asprintf "\\forall %s.%s" (n) (inner false e)
    | Exists (n, NoType, e) -> Format.asprintf "\\exists %s.%s" (n) (inner false e)
    | ForAll (n, t, e) -> Format.asprintf "\\forall %s{:}%s.%s" (n) (type_latex t) (inner false e)
    | Exists (n, t, e) -> Format.asprintf "\\exists %s{:}%s.%s" (n) (type_latex t) (inner false e)
    
    (* Modal *)
    | Let (u, n, m) -> Format.asprintf "\\text{let } %s = %s \\text{ in } %s" (u) (inner false n) (inner false m)
    | Box (NoContext, n, _) -> Format.asprintf "\\square %s" (inner (lt_prec e n) n)
    | Box (c, e, Valid) -> Format.asprintf "[%s]" (context_stmt_latex_base " \\Vdash " c (Utils.no_judge e))
    | Box (c, e, _) -> Format.asprintf "[%s]" (context_stmt_latex_base " \\vdash " c (Utils.no_judge e))
    | NextTime n -> Format.asprintf "\\bigcirc %s" (inner (lt_prec e n) n)
    | CtxExp c -> (context_latex c)

    (* Linear Logic *)
    | LinOne -> "\\mathbb{1}"
    | LinZero -> "\\mathbb{0}"
    | LinAndProd (l, r) -> Format.asprintf "%s \\otimes %s" (inner (le_prec e l) l) (inner  (le_prec e r) r)
    | LinAndSum (l, r) -> Format.asprintf "%s \\mathbin{\\&} %s" (inner (le_prec e l) l) (inner  (le_prec e r) r)
    | LinOrProd (l, r) -> Format.asprintf "%s \\oplus %s" (inner (le_prec e l) l) (inner  (le_prec e r) r)
    | LinOrSum (l, r) -> Format.asprintf "%s \\iamp %s" (inner (le_prec e l) l) (inner  (le_prec e r) r)
    | LinImpl (l, r) -> Format.asprintf "%s \\multimap %s" (inner (le_prec e l) l) (inner  (lt_prec e r) r)
    | Bang n -> Format.asprintf "{!\\,%s}" (inner (lt_prec e n) n)

    (* Continuation *)
    | Control -> "\\mathcal{C}"
    | CallCC -> "\\mathcal{K}"
    | Abort -> "\\mathcal{A}"
    | EvaluationContext ((l,_), (r,_)) -> Format.asprintf "%s[%s]" (inner (lt_prec e l) l) (inner false r)
    in wrap_paran (wrap && (not (expr_is_atomic e))) base)
  in inner false e
and type_latex (t: ty) =   
  let rec inner wrap (t: ty) = 
  (let base = match t with
  | NamedType x -> x
  | UnitType -> "\\top"
  | BottomType -> "\\bot"
  | Sum (l, r) -> Format.asprintf "%s + %s" (inner (ty_le_prec t l) l) (inner (ty_le_prec t r) r)
  | Prod (l, r) -> Format.asprintf "%s \\times %s" (inner (ty_le_prec t l) l) (inner (ty_le_prec t r) r)
  | Func (l, r) -> Format.asprintf "%s \\rightarrow %s" (inner (ty_le_prec t l) l) (inner (ty_lt_prec t r) r)
  | NoType -> failwith ("Try to print NoType Latex")
  in wrap_paran (wrap && (not (type_is_atomic t))) base)
in inner false t
and judgement_latex (j: judgement) = match j with
  |NoJudge -> ""
  |Truth -> " \\text{ true}"
  |Up -> "^{\\uparrow}"
  |Down -> "^{\\downarrow}"
  |Valid -> " \\text{ valid}"
  |TypeOf NoType -> ""
  |TypeOf a -> ":" ^ (type_latex a)
and stmt_latex { exp=le; judge=lj } = (expr_latex le) ^ (judgement_latex lj)
and assumption_latex (ass: assumption) = match ass with
| StmtAssumption (name, st) -> Format.asprintf "%s: %s" (name) (stmt_latex st)
| VariableAssumption (name, jd) -> stmt_latex {exp=Name name; judge=jd}
and context_latex ctx = match ctx with
  | Empty -> "\\,\\cdot\\,"
  | ConName a -> a
  | ConApp (Empty, r) -> Format.asprintf "%s" (assumption_latex r)
  | ConApp (l, r) -> Format.asprintf "%s,%s" (context_latex l) (assumption_latex r)
  | ConCat (l, r) -> Format.asprintf "%s;%s" (context_latex l) (context_latex r)
  | ConNameWithDef (n, _) -> n
  | NoContext -> ""
and context_stmt_latex_base connection ctx st = match ctx with
| NoContext -> stmt_latex st
| _ -> (context_latex ctx) ^ connection ^ (stmt_latex st)

let inference_latex (i: inference) = match i with
  (* Axioms *)
  | Axiom -> ""
  | Law x                                 -> "\\text{"^x^"}"
  | TopIntro                              -> "\\top I"
  | BottomElim                            -> "\\bot E"
  | LinOneElim                            -> "\\mathbb{1}E"
  | LinOneIntro                           -> "\\mathbb{1}I"
  | CtxProof                              -> "\\text{ctx}"
  | Assumption a                          -> a
  | ValidAssumption a                     -> a ^ "*"
  (* Conjunctions *)
  | AndElimLeft  | PairElimLeft           -> "\\land E_l"
  | AndElimRight | PairElimRight          -> "\\land E_r"
  | AndElimAlt (l, r)                     -> Format.asprintf "\\land E^{%s, %s}" l r
  | LinAndProdElim (l, r)                 -> Format.asprintf "\\otimes E^{%s, %s}" l r
  | LetElim x                             -> Format.asprintf "\\text{let}^{%s}" x
  | AndIntro     | PairConstructor        -> "\\land I"
  | LinAndProdIntro                       -> "\\otimes I"
  | LinAndSumIntro                        -> "\\& I"
  | AndLeft1 (_, s)                       -> "\\land L_1^{" ^ s ^"}"
  | AndLeft2 (_, s)                       -> "\\land L_2^{" ^ s ^"}"
  | AndRight                              -> "\\land R"
  | OrRight1                              -> "\\lor R_1"
  | OrRight2                              -> "\\lor R_2"
  | OrLeft  (_,l, r)                      -> Format.asprintf "\\lor L^{%s, %s}" l r
  (* Disjunctions *)
  | OrIntroLeft  | VariantIntroLeft       -> "\\lor Il"
  | OrIntroRight | VariantIntroRight      -> "\\lor Ir"
  | OrElim (l, r)                         -> Format.asprintf "\\lor E^{%s, %s}" l r
  | VariantElim                           -> "\\lor E"
  (* Implication *)
  | ImplIntro a  | LambdaIntro a          -> "{\\supset} I^" ^ a
  | ImplElim     | ApplicationElimination -> "{\\supset} E"
  | ImplLeft  (_, s)                      -> "{\\supset} L^{" ^ s ^"}"
  | ImplRight a                           -> "{\\supset} R^{" ^ a ^"}"
  | LinImplIntro a                        -> "{\\multimap} I^{" ^ a ^"}"
  | LinImplElim                           -> "{\\multimap} E"
  (* Negations *)
  | NotElim                               -> "\\lnot E"
  | NAndElim                              -> "\\overline{\\land} E"
  | NorElim1                              -> "\\overline{\\lor} E_1"
  | NorElim2                              -> "\\overline{\\lor} E_2"
  | NAndIntro (p, l, r)                   -> Format.asprintf "\\overline{\\land} I^{%s, %s, %s}" p l r
  | NorIntro (p, l, q, r)                 -> Format.asprintf "\\overline{\\lor} I^{%s, %s, %s, %s}" p l q r
  | ByContra (l, r)                       -> Format.asprintf "\\text{RAA}^{%s, %s}" l r
  | NotIntro (l, r)                       -> Format.asprintf "\\lnot I^{%s, %s}" l r
  (* For All / Exists *)
  | ForAllIntro (p)                       -> "{\\forall} I^" ^ p
  | ForAllElim                            -> "{\\forall} E"
  | ExistsIntro                           -> "{\\exists} I"
  | ExistsElim (l, r)                     -> Format.asprintf "{\\exists} E^{%s, %s}" l r
  | ForAllRight (p)                       -> "{\\forall} R^" ^ p
  | ForAllLeft (_, _, x)                  -> "{\\forall} L^" ^ x
  | ExistsRight                           -> "{\\exists} R"
  | ExistsLeft (_, l, r)                  -> Format.asprintf "{\\exists} L^{%s, %s}" l r
  (* Box *)
  | BoxIntro                              -> "{\\square} I"
  | BoxElim a                             -> "{\\square} E^{" ^ a ^ "}"
  | BangIntro                             -> "{!\\,} I"
  | BangElim a                            -> "{!\\,} E^{" ^ a ^ "}"
  | NextIntro                             -> "{\\bigcirc} I"
  | NextElim a                            -> "{\\bigcirc} E^{" ^ a ^ "}"
  (* Continuation *)
  | CIntro                                -> "\\mathcal{C}I"
  | CCIntro                               -> "\\text{cc}I"
  | AbortIntro                            -> "\\mathcal{A}I"
  | CElim                                 -> "\\"
  | CCElim                                -> "\\"
  | AbortElim                             -> "\\"
;;

  let rec print_latex_deduction_name (d: deductionName) = match d with
  | Literal x -> x
  | Fancy x -> Format.asprintf "\\mathcal{%s}" x
  | Subscript (x, y) -> Format.asprintf "\\mathcal{%s}_{%s}" x y
  | Substitution (x, y) -> 
    let substitutions = y |> List.map (fun (x, y) -> Format.asprintf "%s/%s" (print_latex_deduction_name x) y)
                         |> String.concat "," in
    Format.asprintf "[%s]%s" substitutions (print_latex_deduction_name x);;

let rec proof_list_latex_base connection (prfs: proof list) = prfs |> List.map (proof_latex_base connection) |> String.concat " & "
and proof_latex_base connection (p: proof) =
  let context_stmt_latex = context_stmt_latex_base connection in
  let valid = wrap_valid (check_flat_correctness p |> Result.is_ok) in
  match !(p.inf) with
  | Inference (i, prfs) ->
      Format.asprintf "\\infer [%s] {%s} {%s}"
      (valid inference_latex i) 
      (context_stmt_latex_base connection p.con p.term)
      (proof_list_latex_base connection prfs)
  | Deduction (s) -> Format.asprintf "\\deduce [] {%s} {%s}" (context_stmt_latex  p.con p.term) (print_latex_deduction_name s)
  | NoInference -> (context_stmt_latex p.con p.term)
and wrap_valid v s x = if v then s x else (Format.asprintf "{\\color{red} %s}" (s x));;

let proof_latex = proof_latex_base " \\vdash ";;
let seq_proof_latex = proof_latex_base " \\Rightarrow ";;

type ctxMap = (string * string) list;;

let rec find_opt k map = match map with
| (target, dest)::tl -> if (target = k) then Some dest else find_opt k tl
| [] -> None

let notation named_ctx = match named_ctx with
| (ConNameWithDef (target, ctx)) -> Format.asprintf "  %s &= %s " target (context_latex  ctx)
| _ -> failwith "Notation Fails with Unnamed Context";;

let rec addCtxToMap (map : ctxMap) named_ctx = 
  match named_ctx with
  | ConNameWithDef (target, sub) ->
    (match find_opt target map with
                  | Some _ -> map
                  | None -> 
                      let new_map = (target, notation named_ctx)::map
                      in addCtxToMap new_map sub
    )
  | ConApp (c, _) -> addCtxToMap map c
  | ConCat (l, r) -> addCtxToMap (addCtxToMap map l) r
  | _ -> map;;


  
let generateCtxMap (p: proof) =
  let rec searchExp (e: expr) (map: ctxMap) = match e with
  | And (l, r)
  | NAnd (l, r)
  | Or (l, r)
  | Impl (l, r) -> 
    let m2 = searchExp l map in
    searchExp r m2
  | Not (r) -> searchExp r map
  | Box (c, r, _) ->
    let added = addCtxToMap map c in 
    searchExp r added
  | _ -> map
  and inner (p: proof) (map: ctxMap) = match p with
  | {con=NoContext; term=e; _} -> searchExp e.exp []
  | {con=c; term=e; inf={ contents = (Inference(_, prfs))} } -> (
    let added = addCtxToMap map c in
    let searched = searchExp e.exp added in
    List.fold_right inner (List.rev prfs) searched)
  | {con=c; term=e; _ } -> searchExp e.exp (addCtxToMap map c)
  in inner p [];;

let compact_latex (p: proof) =
  match generateCtxMap p |> List.map snd with
  | [] -> ""
  | mm -> Format.asprintf
  "For notational compactness, Let:\n\\begin{align*}\n%s\n\\end{align*}\n"
  (String.concat "\\\\ \n" mm)


let compact_latex2 (p: proof) =
  match generateCtxMap p |> List.map snd with
  | [] -> ""
  | mm -> Format.asprintf
  "\\[\n\\begin{alignedat}[b]{3}\n%s\\cdashline{1-4}\n\\end{alignedat}\n\\]"
  (mm 
  |> List.map (Str.global_replace (Str.regexp "\\&") "&&")
  |> List.map (Format.asprintf "&\\text{Let } %s \\\\ \n")
  |> String.concat "")

