open Structs
open Utils
open ContextUtils
open ExprUtils

let rec substitute oldname new_expr expr =
  let rr = substitute oldname new_expr in
  match expr with
  | Name x -> if x = oldname then new_expr else Name x
  | And (l, r) -> And((rr l), (rr r))
  | Or (l, r) ->  Or((rr l), (rr r))
  | Impl (l, r) ->  Impl((rr l), (rr r))
  | Pair (l, r) -> Pair((rr l), (rr r))
  | First e -> First (rr e)
  | Second e -> Second (rr e)
  | Application (l, r) -> Application((rr l), (rr r))
  | Lambda (arg, body) -> 
    if arg = oldname
    then Lambda (arg, body)
    else Lambda (arg, (rr body))
  | LetPair (x, y, p, b) ->
    if (x = oldname || y = oldname) then LetPair (x, y, rr p, b)
    else LetPair (x, y, rr p, rr b)
  | InjectLeft (t, e) -> InjectLeft (t, (rr e))
  | InjectRight (t, e) -> InjectRight (t, (rr e))
  | Case (x, (x1, b1), (x2, b2)) -> Case((rr x), (x1, rr b1), (x2, rr b2))
  | Not (e) -> Not (rr e)
  | NAnd (l, r) -> NAnd((rr l), (rr r))
  | Predicate (n, e) -> Predicate (n, (List.map rr e))
  | ForAll (n, t, e) -> ForAll(n, t, (rr e))
  | Exists (n, t, e) -> Exists(n, t, (rr e))
  | EvaluationContext ((e, t), (v, t2)) -> EvaluationContext((rr e, t), (rr v, t2))
  | x -> x

let rec substitute_proofs oldname new_expr {con=c; term={judge=j;exp=e}; inf=i} = match !i with
  | Inference (i, pfs) ->
    {con=c;
    term={judge=j;exp=(substitute oldname new_expr e)};
    inf=(ref (Inference(i, (List.map (substitute_proofs oldname new_expr) pfs))))}
  | _ ->
    {con=c;
    term={judge=j;exp=(substitute oldname new_expr e)};
    inf=i}

let rec trans (e: expr) : expr = match e with
| Name x -> Name x
| Pair (x, y) -> Pair ((trans x), (trans y))
| First x -> First (trans x)
| Second x -> Second (trans x)
| Application (f, x) -> Application ((trans f), (trans x))
| Lambda (x, m) -> Lambda(x, trans m)
| InjectLeft (ty, e) -> InjectLeft(ty, trans e)
| InjectRight (ty, e) -> InjectLeft(ty, trans e)
| Case (e, (s1, e1), (s2, e2)) -> Case((trans e),
                                       (s1, trans e1),
                                       (s2, trans e2))
| Let (u, n, m) -> Application (Lambda(u, trans m), (trans n))
| _ -> failwith "out of scope";;


let proof_con1 e r ps c = {con=c; term={judge=Truth;exp=e}; inf=(ref (Inference(r, ps)))};;
let proof_con2 e i c = {con=c; term={judge=Truth;exp=e}; inf=(i)};;

let rec print_context (c: context) = match c with
| ConName x -> x
| ConApp (c, StmtAssumption(x, _)) -> (print_context c) ^ "::" ^ x
| ConCat (c1, c2) -> (print_context c1) ^ "::" ^ (print_context c2)
| ConNameWithDef (x, c) -> "("^x^"="^(print_context c)^")"
| _ -> "" 


module TranslationTools = struct
  type mapT = (string * (context -> proof)) list

  let add_to_map (var:string) (p: context -> proof) l = (var, p)::l

  let rec find_in_map (var:string) l: (context -> proof) option = match l with
  | (h, p)::r -> if (h = var) then Some p else find_in_map var r
  | [] -> None

  let is_stmt_ass = function
  | StmtAssumption _ -> true
  | VariableAssumption _ -> false

  let replace_judge (p: judgement -> bool) nJ ({exp=e; judge=j} as s) = match p j with
  | true -> {exp=e; judge=nJ}
  | false -> s

  let cleanse_context_maker ~assPred ~assMap (map: mapT) (con: context) = 
    (List.fold_left (fun c x -> Context.remove_name x c) con (List.map fst map))
        |> Context.transform_by assPred assMap
        |> Context.collapse

  let cleanse_context = cleanse_context_maker ~assPred:(fun _ -> false) ~assMap:Fun.id

  let assumption_or_proof ?(cleanser=cleanse_context) ?(stmtMap=Fun.id) map c var =
    let con = cleanser map c in
    let prf_opt = find_in_map  var map |> Option.map (fun x -> x con) in
    let con_opt = Context.lookupAss var con in
    
    if Option.is_some prf_opt then 
      (Option.get prf_opt)
    else
    match con_opt with
      | Some(StmtAssumption (_, s)) -> use_assumption con var ~st:(stmtMap s)
      | Some(VariableAssumption (n, j)) -> make_proof con {exp=Name n; judge=j} (Assumption n) []
      | _ -> failwith ("Can't find " ^ var ^ " in " ^ (print_context con) ^ " or " ^ (String.concat ", " (List.map fst map)));;

      

  let replace_context c p = {con=c; term=p.term; inf=p.inf};;
end

module SeqTranslatorTools = struct
  include TranslationTools
  let isNoJudge p =  p == NoJudge
  let replace_true = replace_judge isNoJudge Truth

  let replace_true_ass = function
  | StmtAssumption(x, {exp=e; _}) -> StmtAssumption (x, {exp=e; judge=Truth})
  | VariableAssumption(x, _) -> VariableAssumption (x, Truth);;
  
  let cleanse_context = cleanse_context_maker ~assPred:is_stmt_ass ~assMap:replace_true_ass

  let assumption_or_proof = TranslationTools.assumption_or_proof
    ~cleanser:cleanse_context
    ~stmtMap:replace_true
end

module CurryTranslatorTools = struct
  include TranslationTools
  module StringSet = Set.Make(String)

  let termNames = List.init 13 (fun i -> Char.escaped(Char.chr (int_of_char 'M' + i)))
  let typeNames = List.init 12 (fun i -> Char.escaped(Char.chr (int_of_char 'A' + i)))

  let get_new_term_name (used: StringSet.t) =
    let newName = List.find (fun element -> not (StringSet.mem element used)) termNames in
    (newName, StringSet.add newName used)
  
    let get_new_type_name (used: StringSet.t) =
    let newName = List.find (fun element -> not (StringSet.mem element used)) typeNames in
    (newName, StringSet.add newName used)

  let rec expr_to_type ?default e = match e with
  | Top -> UnitType
  | And (l, r) -> Prod(expr_to_type ?default:default l, expr_to_type ?default:default r)
  | Or (l, r) -> Sum(expr_to_type ?default:default l, expr_to_type ?default:default r)
  | Impl (l, r) -> Func(expr_to_type ?default:default l, expr_to_type ?default:default r)
  | Not (l) -> Func(expr_to_type l, BottomType)
  | Bottom -> BottomType
  | Name x -> NamedType x
  | _ -> match default with
    | Some x -> x
    | _ -> failwith "Expression has no equivalent type"
  

  let replace_ass ?default = function
  | StmtAssumption(x, {exp=e; _}) -> VariableAssumption (x, TypeOf(expr_to_type ?default:default e))
  | VariableAssumption _ as v -> v;;

  let cleanse_context ?default = cleanse_context_maker ~assPred:is_stmt_ass ~assMap:(replace_ass ?default)

    let assumption_or_proof = TranslationTools.assumption_or_proof
    ~cleanser:cleanse_context
    ~stmtMap:Fun.id
end

let rec seq_to_nat (p: proof) : proof =
  let open SeqTranslatorTools in

  let rec seq_to_nat_with_map map ({con=c0; term={judge=_;exp=e}; inf=i}: proof) : proof =
    let c = cleanse_context map c0
    in
    let map_sub_proofs = List.map (seq_to_nat_with_map map) in
    match !i with
    | Inference((Assumption x), _) -> assumption_or_proof map c0 x
    | Inference((AndRight), pfs) -> proof_con1  e AndIntro (map_sub_proofs pfs) c
    | Inference((OrRight1), pfs) -> proof_con1  e OrIntroLeft (map_sub_proofs pfs) c
    | Inference((OrRight2), pfs) -> proof_con1  e OrIntroRight (map_sub_proofs pfs) c
    | Inference((ForAllRight x), pfs) -> proof_con1  e (ForAllIntro x) (map_sub_proofs pfs) c
    | Inference((ImplRight x), pfs) -> proof_con1  e (ImplIntro x) (map_sub_proofs pfs) c
    
    | Inference((ImplLeft (u, v)), [pl; pr]) ->
      let impl = Option.get (Context.lookupStmt u c) in
      let b_stmt = Option.get(Context.lookupStmt v pl.con) in
      let a_proof = seq_to_nat pr in
      let impl_proof = use_assumption c u ~st:impl in
      let b_proof = proof_con1  b_stmt.exp (ImplElim) [impl_proof; a_proof] c in
      
      let c_proof = seq_to_nat pl in
      let b_to_c_proof = proof_con1  (Impl (b_stmt.exp, e)) (ImplIntro v) [c_proof] c in
      let ret = proof_con1  e (ImplElim) [b_to_c_proof; b_proof] c in
      
      if Equality.expr_eq_b b_stmt.exp e then b_proof else ret
    | Inference((AndLeft1 (x, y)), [pf]) ->
      let extracted = Option.get (Context.lookupStmt y pf.con) in
      let construct_proof c2 = (
        let and_proof = assumption_or_proof map c2 x in
        proof_con1 extracted.exp AndElimLeft [and_proof] c2
      ) in
      seq_to_nat_with_map (add_to_map y construct_proof map) (replace_context c pf)
    | Inference((AndLeft2 (x, y)), [pf]) ->
      let extracted = Option.get (Context.lookupStmt y pf.con) in
      let construct_proof c2 = (
        let and_proof = assumption_or_proof map c2 x in
        proof_con1 extracted.exp AndElimRight [and_proof] c2
      ) in
      seq_to_nat_with_map (add_to_map y construct_proof map) (replace_context c pf)
    | Inference((OrLeft (u, v, w)), [pfl; pfr]) ->
      let or_proof = assumption_or_proof map c u in
      proof_con1  e (OrElim(v, w)) (or_proof::(map_sub_proofs [pfl; pfr])) c

    | Inference((ForAllLeft (src, rep, dest)), [pup]) ->
      (* let forall_proof = assumption_or_proof map c src in *)
      let rep_proof = assumption_or_proof map c rep in
      let extracted = Option.get (Context.lookupStmt dest pup.con) in
      let construct_proof c2 = (
        let forall_proof = assumption_or_proof map c2 src in
        proof_con1 extracted.exp ForAllElim [rep_proof; forall_proof] c2
      ) in
      seq_to_nat_with_map (add_to_map dest construct_proof map) (replace_context c pup)

    | NoInference
    | Deduction _ 
      -> {con=c; term={judge=Truth;exp=e}; inf=i}
    | _ -> failwith ("Invalid Seq Inference") in
  seq_to_nat_with_map [] p 

let nat_to_curry ?(strict=true) (p: proof) : proof = 
  let open CurryTranslatorTools in
  let default_type = if strict then None else Some (NamedType "?") in
  
  let rec nat_to_curry_with_used (used: StringSet.t) ({con=c0; term={judge=_;exp=e}; inf=i}: proof) : (StringSet.t * proof) =
    let c = cleanse_context ?default:default_type [] c0
    in
    match !i with
    | Inference((Assumption x), []) -> 
       used, (assumption_or_proof [] c x)
    | Inference((AndIntro), [pfL; pfR]) ->
       let (used2, trPL) = nat_to_curry_with_used used pfL in
       let (used3, trPR) = nat_to_curry_with_used used2 pfR in
       used3, (make_proof trPR.con  CurryExpr.(trPL.term & trPR.term) PairConstructor [trPL; trPR])
    | Inference((AndElimLeft), [pf]) ->
       let (used2, trP) = nat_to_curry_with_used used pf in
       used2, (make_proof trP.con  CurryExpr.(?< (trP.term)) PairElimLeft [trP])
    | Inference((AndElimRight), [pf]) ->
       let (used2, trP) = nat_to_curry_with_used used pf in
       used2, (make_proof trP.con  CurryExpr.(?> (trP.term)) PairElimRight [trP])
    | Inference((ImplIntro x), [pf]) ->
       let (used2, trP) = nat_to_curry_with_used used pf in
       let var_ass = match Context.lookupAss x trP.con with
       | Some (VariableAssumption (n, TypeOf t)) -> n, t
       | _ -> failwith "Var not in context"
        in
       used2, (make_proof c  CurryExpr.( var_ass /=> (trP.term)) (LambdaIntro x) [trP])
    | Inference((ImplElim), [pfl; pfr]) ->
       let (used2, trPL) = nat_to_curry_with_used used pfl in
       let (used3, trPR) = nat_to_curry_with_used used2 pfr in
       used3, (make_proof c  CurryExpr.( (trPL.term) @ (trPR.term)) (ApplicationElimination) [trPL; trPR])
    | Inference((OrIntroLeft), [pf]) ->
       let sumTy = expr_to_type e in
       let (used2, trP) = nat_to_curry_with_used used pf in
       used2, (make_proof trP.con  CurryExpr.(injL (extractRight sumTy) (trP.term)) (VariantIntroLeft ) [trP])
    | Inference((OrIntroRight), [pf]) ->
      let sumTy = expr_to_type e in
      let (used2, trP) = nat_to_curry_with_used used pf in
      used2, (make_proof trP.con  CurryExpr.(injR (extractLeft sumTy) (trP.term)) VariantIntroRight [trP])
    | Inference((OrElim (a, b)), [pf1; pf2; pf3]) ->
      let (used2, trP1) = nat_to_curry_with_used used pf1 in
      let (used3, trP2) = nat_to_curry_with_used used2 pf2 in
      let (used4, trP3) = nat_to_curry_with_used used3 pf3 in
      used4, (make_proof c  CurryExpr.(caseStmt trP1.term a trP2.term b trP3.term) VariantElim [trP1; trP2; trP3])
    | Inference((BottomElim), [pf1]) ->
      let (used2, trP1) = nat_to_curry_with_used used pf1 in
      used2, (make_proof c CurryExpr.(abortTyped trP1.term.exp (expr_to_type e)) AbortIntro [trP1])
    | Inference((Law "Peirce"), []) ->
      used, (make_proof c (Utils.is_type CallCC (expr_to_type e)) CCIntro [])
    | NoInference
    | Deduction _ 
      ->
        let term, used2 = get_new_term_name used in
        (used2, {con=c; term={judge=TypeOf (expr_to_type ?default:default_type e);exp=Name term}; inf=i})
    | _ -> 
      if strict then
        failwith ("Invalid Nat Ded Inference")
      else
        let x, used1 = get_new_term_name used in
        let t = PrettyPrinter.pp_expr e in
        used1, {con=c; term={judge=TypeOf (expr_to_type e ~default:(NamedType t)); exp=(Name x)}; inf=ref (Inference(Axiom, []))}
      in
  snd(nat_to_curry_with_used StringSet.empty p)



