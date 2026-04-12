open Structs
module StringSet = Set.Make (String)

let vars = List.init 26 (fun i -> Char.escaped (Char.chr (int_of_char 'a' + i)))

let greek_vars_small =
  [
    "\\alpha";
    "\\beta";
    "\\gamma";
    "\\delta";
    "\\epsilon";
    "\\zeta";
    "\\theta";
    "\\iota";
    "\\kappa";
    "\\nu";
    "\\xi";
    "\\pi";
    "\\rho";
    "\\sigma";
    "\\tau";
    "\\upsilon";
    "\\phi";
    "\\chi";
    "\\psi";
    "\\omega";
  ]

let make_multi base =
  Seq.(
    append (List.to_seq base)
      (concat
         (List.to_seq base
         |> map (fun c -> map (fun x -> c ^ x) (List.to_seq base)))))

let char_vars2 = make_multi vars
let anon_vars2 = make_multi (vars |> List.map (( ^ ) "_"))
let greek_vars2 = make_multi greek_vars_small

let rec collect_vars = function
  | Name x -> StringSet.singleton x
  | Pair (l, r) | Application (l, r) | EvaluationContext (l, r) ->
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

let find_unique_var ?(varset = char_vars2) ?(used = StringSet.empty) e =
  let names = collect_vars e in
  Option.value ~default:"\\_\\_x"
    (Seq.find
       (fun x -> not (StringSet.mem x names || StringSet.mem x used))
       varset)

let find_unique_vars ?(varset = char_vars2) count e =
  let names = collect_vars e in
  Array.of_seq
    Seq.(varset |> filter (fun x -> not (StringSet.mem x names)) |> take count)
