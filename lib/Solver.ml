open Structs
open Translator
open Utils
open ContextUtils

let complete_proof p i = p.inf := i
let make_inference p r ps = p.inf := Inference (r, ps)
let prove_with_deduction p ps = p.inf := Deduction (Literal ps)
let prove_with_assumption name p = p.inf := with_assumption name

type proof_resolver = inference -> proof

module StringSet = Set.Make (String)

module BaseSolver (Ctx : ContextFunctions) = struct
  (* GENERATING NAMES *)
  let get_used_names (c : context) =
    let rec recursive (c : context) =
      match c with
      | ConApp (sub, StmtAssumption (a, _))
      | ConApp (sub, VariableAssumption (a, _)) ->
          StringSet.add a (recursive sub)
      | ConCat (l, r) -> StringSet.union (recursive l) (recursive r)
      | ConNameWithDef (_, sub) -> recursive sub
      | Empty | ConName _ | NoContext -> StringSet.empty
    in
    recursive c

  let variable_names =
    List.init 6 (fun i -> Char.escaped (Char.chr (int_of_char 'u' + i)))
    @ List.init 20 (fun i -> Char.escaped (Char.chr (int_of_char 'a' + i)))

  let find_valid_name names (c : context) =
    match names with
    | n :: rest -> (n, rest)
    | [] ->
        let used = get_used_names c in
        let newname =
          List.find
            (fun element -> not (StringSet.mem element used))
            variable_names
        in
        (newname, names)

  (* GENERATING PROOFS *)
  let make_partial_t c t = { con = c; term = t; inf = ref NoInference }
  let make_term e j = { exp = e; judge = j }

  let make_partial_e c e j =
    { con = c; term = make_term e j; inf = ref NoInference }

  let make_empty = make_partial_t Ctx.empty

  let wrap_context (name : string option) (c : context) =
    match name with None -> c | Some x -> Ctx.name x c
end

module NatDedSolver (Ctx : ContextFunctions) = struct
  include BaseSolver (Ctx)

  let split ?(version = 1) ?ctxName ?(vars = []) (p : proof) =
    match p with
    | { con = c; term = { exp = And (l, r); judge = j }; _ } ->
        let to_return = [ make_partial_e c l j; make_partial_e c r j ] in
        p.inf := Inference (AndIntro, to_return);
        to_return
    | { con = c; term = { exp = Impl (l, r); judge = j }; _ } ->
        let new_var, _ = find_valid_name vars c in
        let new_ctx =
          wrap_context ctxName (Ctx.add new_var (make_term l j) c)
        in
        let to_return = [ make_partial_e new_ctx r j ] in
        p.inf := Inference (ImplIntro new_var, to_return);
        to_return
    | { con = c; term = { exp = Not e; judge = j }; _ } ->
        let pName, pExp, vars =
          match (version, vars) with
          | 1, targetname :: rest1 -> (targetname, Name targetname, rest1)
          | _ -> ("\\bot", Bottom, vars)
        in
        let new_var, _ = find_valid_name vars c in
        let new_ctx =
          wrap_context ctxName (Ctx.add new_var (make_term e j) c)
        in
        let to_return = [ make_partial_e new_ctx pExp j ] in
        p.inf := Inference (NotIntro (pName, new_var), to_return);
        to_return
    | { con = c; term = { exp = NAnd (l, r); judge = j }; _ } -> (
        match vars with
        | targetname :: rest1 ->
            let new_var1, rest2 = find_valid_name rest1 c in
            let new_var2, _ = find_valid_name rest2 c in
            let new_ctx1 =
              wrap_context None (Ctx.add new_var1 (make_term l j) c)
            in
            let new_ctx2 =
              wrap_context ctxName (Ctx.add new_var2 (make_term r j) new_ctx1)
            in
            let to_return = [ make_partial_e new_ctx2 (Name targetname) j ] in
            p.inf :=
              Inference (NAndIntro (targetname, new_var1, new_var2), to_return);
            to_return
        | _ -> failwith "Too Few Names")
    | { con = c; term = { exp = Nor (l, r); judge = j }; _ } -> (
        match vars with
        | target1 :: target2 :: rest1 ->
            let new_var1, rest2 = find_valid_name rest1 c in
            let new_var2, _ = find_valid_name rest2 c in
            let new_ctx1 =
              wrap_context None (Ctx.add new_var1 (make_term l j) c)
            in
            let new_ctx2 =
              wrap_context None (Ctx.add new_var2 (make_term r j) c)
            in
            let to_return =
              [
                make_partial_e new_ctx1 (Name target1) j;
                make_partial_e new_ctx2 (Name target2) j;
              ]
            in
            p.inf :=
              Inference
                (NorIntro (target1, new_var1, target2, new_var2), to_return);
            to_return
        | _ -> failwith "Too Few Names")
    | { con = c; term = { exp = ForAll (n, t, e); judge = j }; _ } ->
        let new_var, _ = find_valid_name vars c in
        let new_ctx = wrap_context ctxName (Ctx.add_var new_var (TypeOf t) c) in
        let to_return =
          [ make_partial_e new_ctx (substitute n (Name new_var) e) j ]
        in
        p.inf := Inference (ForAllIntro new_var, to_return);
        to_return
    | _ -> failwith "Bad Split"

  let proof_by_conta ?ctxName ?(vars = []) (p : proof) =
    match p with
    | { con = c; term = { exp = e; judge = j }; _ } -> (
        match vars with
        | targetname :: rest1 ->
            let new_var, _ = find_valid_name rest1 c in
            let new_ctx =
              wrap_context ctxName (Ctx.add new_var (make_term (Not e) j) c)
            in
            let to_return = [ make_partial_e new_ctx (Name targetname) j ] in
            p.inf := Inference (ByContra (targetname, new_var), to_return);
            to_return
        | _ -> failwith "Too Few Names")
end

module ModalSolver (Ctx : ContextFunctions) = struct
  module Super = NatDedSolver (Ctx)
  include BaseSolver (Ctx)

  let _split_ctx ctx =
    match ctx with
    | ConCat (l, r) -> (l, r)
    | _ -> failwith "Failed to Split Context"

  let split ?ctxName ?(vars = []) (p : proof) =
    match p with
    | { con = ConCat (l, _); term = { exp = Box (c2, e, _); judge = j }; _ } ->
        let newCtx = ConCat (l, Context.reifyContext c2) in
        let to_return = [ make_partial_e newCtx e j ] in
        p.inf := Inference (BoxIntro, to_return);
        to_return
    | { con = c; term = { exp = NextTime n; judge = j }; _ } ->
        let new_ctx = TemporalContext.next c in
        let to_return = [ make_partial_e new_ctx n j ] in
        p.inf := Inference (NextIntro, to_return);
        to_return
    | { con = c; term = { exp = CtxExp sub; _ }; _ } ->
        let _extract_statment = function
          | StmtAssumption (_, s) -> s
          | _ -> failwith "Only Valid for Statement Assumptions"
        in
        let to_return =
          Ctx.flatten sub |> List.map _extract_statment
          |> List.map (make_partial_t c)
        in
        p.inf := Inference (CtxProof, to_return);
        to_return
    | _ -> Super.split ?ctxName ~vars p

  let unbox ctx name new_name ?(newJudge = Valid) ?ctxName p =
    let _, r = _split_ctx ctx in
    let stmt =
      match Ctx.lookupStmt name r with
      | Some { exp = Box (NoContext, e, _); _ } -> { exp = e; judge = newJudge }
      | Some { exp = Box (c, e, _); _ } ->
          { exp = Box (c, e, Valid); judge = newJudge }
      | _ -> failwith "Variable is not boxed"
    in
    let box_proof = use_assumption ctx name in
    let ctx2 =
      match ctxName with
      | Some cName ->
          ModalContext.(add ~alt:ValidCTX new_name stmt ctx |> nameLeft cName)
      | None -> ModalContext.add ~alt:ValidCTX new_name stmt ctx
    in
    let next_proof = make_partial_t ctx2 p.term in
    make_inference p (BoxElim new_name) [ box_proof; next_proof ];
    [ box_proof; next_proof ]

  let assumption_elimination var_name ({ con = c; _ } as p) =
    let l, _ = _split_ctx c in
    let cubC, eTerm =
      match Ctx.lookupStmt var_name l with
      | Some { exp = Box (c2, e, Valid); _ } -> (c2, e)
      | _ -> failwith "Variable is Found in Valid Context"
    in
    if not (Equality.expr_eq_b eTerm p.term.exp) then
      failwith "Expression Doesn't Match"
    else
      let next_proof = make_partial_e c (CtxExp cubC) NoJudge in
      make_inference p (ValidAssumption var_name) [ next_proof ];
      next_proof
end

module SeqSolver (Ctx : ContextFunctions) = struct
  include BaseSolver (Ctx)

  let split_right ?(v = 1) ?ctxName ?(vars = []) (p : proof) =
    match p with
    | { con = c; term = { exp = Impl (l, r); judge = j }; _ } ->
        let new_var, _ = find_valid_name vars c in
        let new_ctx =
          wrap_context ctxName (Ctx.add new_var (make_term l j) c)
        in
        let to_return = [ make_partial_e new_ctx r j ] in
        p.inf := Inference (ImplRight new_var, to_return);
        to_return
    | { con = c; term = { exp = Or (l, r); judge = j }; _ } ->
        let e = if v == 1 then l else r in
        let rule = if v == 1 then OrRight1 else OrRight2 in
        let to_return = [ make_partial_e c e j ] in
        p.inf := Inference (rule, to_return);
        to_return
    | { con = c; term = { exp = And (l, r); judge = j }; _ } ->
        let to_return = [ make_partial_e c l j; make_partial_e c r j ] in
        p.inf := Inference (AndRight, to_return);
        to_return
    | { con = c; term = { exp = ForAll (x, t, e); judge = j }; _ } ->
        let new_var, _ = find_valid_name vars c in
        let new_right = substitute x (Name new_var) e in
        let new_ctx = wrap_context ctxName (Ctx.add_var new_var (TypeOf t) c) in
        let to_return = [ make_partial_e new_ctx new_right j ] in
        p.inf := Inference (ForAllRight new_var, to_return);
        to_return
    | _ -> failwith "Unsupported Seq Split Right"

  let split_left ?(v = 1) (names : (string option * string list) list) variable
      (p : proof) =
    let stmt = Ctx.lookupStmt variable p.con in
    match (names, p, stmt) with
    | ( (ctxName, vars) :: _,
        { con = c; term = { exp = e; judge = j }; _ },
        Some { exp = And (l, r); _ } ) ->
        let new_var, _ = find_valid_name vars c in
        let new_ctx =
          wrap_context ctxName
            (Ctx.add new_var (make_term (if v = 1 then l else r) j) c)
        in
        let to_return = [ make_partial_e new_ctx e j ] in
        p.inf :=
          Inference
            ( (if v = 1 then AndLeft1 (variable, new_var)
               else AndLeft2 (variable, new_var)),
              to_return );
        to_return
    | ( (ctxName1, vars1) :: (ctxName2, vars2) :: _,
        { con = c; term = { exp = e; judge = j }; _ },
        Some { exp = Or (l, r); _ } ) ->
        let new_var1, _ = find_valid_name vars1 c in
        let new_var2, _ = find_valid_name vars2 c in
        let new_ctx1 =
          wrap_context ctxName1 (Ctx.add new_var1 (make_term l j) c)
        in
        let new_ctx2 =
          wrap_context ctxName2 (Ctx.add new_var2 (make_term r j) c)
        in
        let to_return =
          [ make_partial_e new_ctx1 e j; make_partial_e new_ctx2 e j ]
        in
        p.inf := Inference (OrLeft (variable, new_var1, new_var2), to_return);
        to_return
    | ( (ctxName, vars) :: _,
        { con = c; term = { exp = e; judge = j }; _ },
        Some { exp = Impl (l, r); _ } ) ->
        let new_var1, _ = find_valid_name vars c in
        let new_ctx1 =
          wrap_context ctxName (Ctx.add new_var1 (make_term r j) c)
        in
        let to_return = [ make_partial_e new_ctx1 e j; make_partial_e c l j ] in
        p.inf := Inference (ImplLeft (variable, new_var1), to_return);
        to_return
    | ( (None, [ a ]) :: (ctxName, vars) :: _,
        { con = c; term = { exp = e; judge = j }; _ },
        Some { exp = ForAll (x, t0, pred); _ } ) ->
        let sub_expr =
          match Ctx.lookupStmt a c with
          | Some { judge = TypeOf t1; exp = s } ->
              if t1 == t0 then s
              else
                failwith
                  (Format.asprintf "variable %s is not the correct type" a)
          | _ ->
              failwith (Format.asprintf "variable %s is not the correct type" a)
        in
        let new_var1, _ = find_valid_name vars c in
        let new_ctx1 =
          wrap_context ctxName
            (Ctx.add new_var1 (make_term (substitute x sub_expr pred) j) c)
        in
        let to_return = [ make_partial_e new_ctx1 e j ] in
        p.inf := Inference (ForAllLeft (variable, a, new_var1), to_return);
        to_return
    | _ -> failwith "Unsupported Seq Split Left"
end

module LinearSolver (Ctx : ContextFunctions) = struct
  include BaseSolver (Ctx)

  let _split_ctx ctx =
    match ctx with
    | ConCat (l, r) -> (l, r)
    | _ -> failwith "Failed to Split Context"

  let split ?(ctxName = []) ?(vars = []) ?(extract_names = []) (p : proof) =
    match p with
    | { con = c; term = { exp = LinImpl (l, r); judge = j }; _ } ->
        let new_var, _ = find_valid_name vars c in
        let new_ctx =
          wrap_context (List.nth_opt ctxName 0)
            (Ctx.add new_var (make_term l j) c)
        in
        let to_return = [ make_partial_e new_ctx r j ] in
        p.inf := Inference (LinImplIntro new_var, to_return);
        to_return
    | { con = c; term = { exp = LinAndProd (l, r); judge = j }; _ } ->
        let c1, c2 = Ctx.extract_names extract_names c in
        let to_return =
          [
            make_partial_e (wrap_context (List.nth_opt ctxName 0) c1) l j;
            make_partial_e (wrap_context (List.nth_opt ctxName 1) c2) r j;
          ]
        in
        p.inf := Inference (LinAndProdIntro, to_return);
        to_return
    | { con = c; term = { exp = LinAndSum (l, r); judge = j }; _ } ->
        let to_return = [ make_partial_e c l j; make_partial_e c r j ] in
        p.inf := Inference (LinAndSumIntro, to_return);
        to_return
    | { con = Empty; term = { exp = LinOne; judge = _ }; _ } ->
        p.inf := Inference (LinOneIntro, []);
        []
    | { con = ConCat (l, Empty); term = { exp = Bang e; judge = j }; _ } ->
        let to_ret = [ make_partial_e l e j ] in
        p.inf := Inference (BangIntro, to_ret);
        to_ret
    | _ -> failwith "Bad Split"

  let unbang ctx name new_name ?(newJudge = Valid) ?(ctxName = []) p =
    let _, r = _split_ctx ctx in
    let stmt =
      match Ctx.lookupStmt name r with
      | Some { exp = Bang e; _ } -> { exp = e; judge = newJudge }
      | _ -> failwith "Variable is not boxed"
    in
    let ll, rr = ModalContext.extract_names [ name ] ctx in
    let ctx1 =
      match List.nth_opt ctxName 2 with
      | Some cName -> ModalContext.(ll |> nameRight cName)
      | None -> ll
    in
    let ctx2 =
      match List.nth_opt ctxName 0 with
      | Some cName ->
          ModalContext.(rr |> add ~alt:ValidCTX new_name stmt |> nameLeft cName)
      | None -> ModalContext.(rr |> add ~alt:ValidCTX new_name stmt)
    in
    let ctx3 =
      match List.nth_opt ctxName 1 with
      | Some cName -> ModalContext.(ctx2 |> nameRight cName)
      | None -> ctx2
    in
    let box_proof = use_assumption ctx1 name in
    let next_proof = make_partial_t ctx3 p.term in
    make_inference p (BangElim new_name) [ box_proof; next_proof ];
    [ box_proof; next_proof ]
end

module ControlSolver (Ctx : ContextFunctions) = struct
  include BaseSolver (Ctx)
end

module CCCSolver (Ctx : ContextFunctions) = struct
  include BaseSolver (Ctx)
end
