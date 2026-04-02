open Structs

let ass_name (ctx : context) =
  match ctx with
  | ConApp (_, StmtAssumption (a, _))
  | ConApp (_, VariableAssumption (a, _))
  | ConNameWithDef (_, ConApp (_, StmtAssumption (a, _)))
  | ConNameWithDef (_, ConApp (_, VariableAssumption (a, _))) ->
      a
  | _ -> failwith "No New Assumption"

let prev_ctx (ctx : context) =
  match ctx with
  | ConApp (a, _) -> a
  | ConNameWithDef (_, ConApp (a, _)) -> a
  | _ -> failwith "No New Assumption"

let ass_names ctx num =
  let rec inner ctx num acc =
    match num with
    | 0 -> acc
    | _ ->
        let name = ass_name ctx in
        let sub = prev_ctx ctx in
        inner sub (num - 1) (name :: acc)
  in
  inner ctx num []

let asses_to_lam ctx num =
  ass_names ctx num |> List.map (Format.asprintf "\\%s.") |> String.concat ""

let wrap b text =
  match b with true -> Format.asprintf "(%s)" text | false -> text

let sym_map_basic d =
  match d with
  | AndElimLeft -> "∧El"
  | AndElimRight -> "∧Er"
  | AndIntro -> "∧I"
  | OrIntroLeft -> "∨Il"
  | OrIntroRight -> "∨Ir"
  | OrElim (_, _) -> "∨E"
  | ImplIntro _ -> "⊃I"
  | ImplElim -> "⊃E"
  | NotIntro _ -> "¬I"
  | NotElim -> "¬E"
  | NAndElim -> "⊼E"
  | ForAllIntro _ -> "∀I"
  | ForAllElim -> "∀E"
  | ExistsIntro -> "∃I"
  | ExistsElim _ -> "∃E"
  | NAndIntro (_, _, _) -> "⊼I"
  | Assumption x -> x
  | _ -> failwith "Invalid symbolic basic mapping"

let sym_map_seq d =
  match d with
  | AndLeft1 _ -> "∧L1"
  | AndLeft2 _ -> "∧L2"
  | AndRight -> "∧R"
  | OrRight1 -> "∨R1"
  | OrRight2 -> "∨R2"
  | OrLeft _ -> "∨L"
  | ImplRight _ -> "⊃R"
  | ImplLeft _ -> "⊃L"
  | ForAllRight _ -> "∀R"
  | ForAllLeft _ -> "∀L"
  | Assumption x -> Format.asprintf "(initial %s)" x
  | _ -> failwith "Invalid symbolic sequence mapping"

let sym_map_alt d =
  match d with
  | AndElimAlt (_, _) -> "∧nE"
  | AndIntro -> "∧nI"
  | OrIntroLeft -> "∨nIl"
  | OrIntroRight -> "∨nIr"
  | OrElim (_, _) -> "∨nE"
  | ImplIntro _ -> "⊃nI"
  | ImplElim -> "⊃nE"
  | Assumption x -> x
  | _ -> failwith "Invalid symbolic alt mapping"

let cnd_mapping d =
  match d with
  | AndElimLeft -> "∧cEl"
  | AndElimRight -> "∧cEr"
  | AndIntro -> "∧cI"
  | OrIntroLeft -> "∨cIl"
  | OrIntroRight -> "∨cIr"
  | OrElim (_, _) -> "∨cE"
  | ImplIntro _ -> "⊃cI"
  | ImplElim -> "⊃cE"
  | NotIntro _ -> "¬cI"
  | NotElim -> "¬cE"
  | ByContra _ -> "byContra"
  | Assumption x -> x
  | _ -> failwith "Invalid symbolic cnd mapping"

let rec print_bel_deduction_name (d : deductionName) =
  match d with
  | Literal x | Fancy x -> x
  | Subscript (x, "\\text{weak}") -> x ^ "[..]"
  | Subscript (x, y) -> x ^ y
  | Substitution (x, y) ->
      let substitutions =
        y |> List.map fst
        |> List.map print_bel_deduction_name
        |> String.concat ","
      in
      Format.asprintf "%s[..,%s]" (print_bel_deduction_name x) substitutions

let print_bel_ctx (ctx : context) =
  match ctx with
  | ConName "\\Gamma" | ConNameWithDef ("\\Gamma", _) -> " Γ"
  | ConName "\\Gamma'" | ConNameWithDef ("\\Gamma'", _) -> " Γ'"
  | ConName x | ConNameWithDef (x, _) -> x
  | Empty -> ""
  | _ -> failwith "Complex Context not implemented yet for beluga"

let proof_bel_base mapping (prf : proof) =
  let rec inner (p : proof) simple =
    match !(p.inf) with
    | Inference (i, pfs) -> (
        match (p.term, i, pfs) with
        | _, Assumption _, [] -> mapping i
        | _, AndElimRight, [ p1 ] | _, AndElimLeft, [ p1 ] ->
            wrap simple (Format.asprintf "%s %s" (mapping i) (inner p1 true))
        | _, AndElimAlt (_, _), [ pl; pr ] ->
            wrap simple
              (Format.asprintf "%s %s %s%s" (mapping i) (inner pl true)
                 (asses_to_lam pr.con 2) (inner pr false))
        | _, ByContra (target, s), [ pr ] | _, NotIntro (target, s), [ pr ] ->
            wrap simple
              (Format.asprintf "%s \\%s.\\%s.%s" (mapping i) target s
                 (inner pr false))
        | _, NAndIntro (target, a, b), [ pr ] ->
            wrap simple
              (Format.asprintf "%s \\%s.\\%s.\\%s.%s" (mapping i) target a b
                 (inner pr false))
        | _, NotElim, [ pl; pr ]
        | _, AndIntro, [ pl; pr ]
        | _, AndRight, [ pl; pr ] ->
            wrap simple
              (Format.asprintf "%s %s %s" (mapping i) (inner pl true)
                 (inner pr true))
        | _, OrIntroLeft, [ p1 ]
        | _, OrIntroRight, [ p1 ]
        | _, OrRight1, [ p1 ]
        | _, OrRight2, [ p1 ] ->
            wrap simple (Format.asprintf "%s %s" (mapping i) (inner p1 true))
        | _, OrElim (_, _), [ p1; pl; pr ] ->
            wrap simple
              (Format.asprintf "%s %s (\\%s.%s) (\\%s.%s)" (mapping i)
                 (inner p1 true) (ass_name pl.con) (inner pl false)
                 (ass_name pr.con) (inner pr false))
        | _, ImplIntro s, [ p1 ] | _, ImplRight s, [ p1 ] ->
            wrap simple
              (Format.asprintf "%s \\%s.%s" (mapping i) s (inner p1 false))
        | _, ImplElim, [ p1; a ] ->
            wrap simple
              (Format.asprintf "%s %s %s" (mapping i) (inner p1 true)
                 (inner a true))
        | _, NAndElim, [ n; a; b ] ->
            wrap simple
              (Format.asprintf "%s %s %s %s" (mapping i) (inner n true)
                 (inner a true) (inner b true))
        | { exp = Exists (_, _, _); _ }, ExistsIntro, [ t; b ] ->
            wrap simple
              (Format.asprintf "%s %s %s" (mapping i) (inner t true)
                 (inner b true))
        | _, ExistsElim (t, w), [ u; a ] ->
            wrap simple
              (Format.asprintf "%s %s (\\%s.\\%s.%s)" (mapping i) (inner u true)
                 t w (inner a true))
        | _, ForAllElim, [ t; b ] ->
            wrap simple
              (Format.asprintf "%s %s %s" (mapping i) (inner t true)
                 (inner b true))
        | _, ForAllIntro a, [ t ] | _, ForAllRight a, [ t ] ->
            wrap simple
              (Format.asprintf "%s \\%s.%s" (mapping i) a (inner t true))
        | _, AndLeft2 (src, dest), [ p1 ] | _, AndLeft1 (src, dest), [ p1 ] ->
            wrap simple
              (Format.asprintf "(%s \\%s.%s) %s" (mapping i) dest
                 (inner p1 false) src)
        | _, OrLeft (src, d1, d2), [ pl; pr ] ->
            wrap simple
              (Format.asprintf "(%s (\\%s.%s) (\\%s.%s)) %s" (mapping i) d1
                 (inner pl false) d2 (inner pr false) src)
        | _, ImplLeft (src, d), [ pl; pr ] ->
            wrap simple
              (Format.asprintf "(%s %s \\%s.%s) %s" (mapping i) (inner pr true)
                 d (inner pl false) src)
        | _, ForAllLeft (src, t, dest), [ p ] ->
            wrap simple
              (Format.asprintf "(%s %s \\%s.%s) %s" (mapping i) t dest
                 (inner p false) src)
        | _ -> "(?)")
    | Deduction s -> Format.asprintf "%s" (print_bel_deduction_name s)
    | _ -> "(?)"
  in
  Format.asprintf "[%s ⊢ %s ]" (print_bel_ctx prf.con) (inner prf false)

let proof_bel = proof_bel_base sym_map_basic
let proof_bel_alt = proof_bel_base sym_map_alt
let proof_bel_classic = proof_bel_base sym_map_alt
