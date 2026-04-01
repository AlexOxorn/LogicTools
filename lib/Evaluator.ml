open Structs;;

let stmt_to_exp_ty = function
| {exp=e; judge=TypeOf t} -> e, t
| _ -> failwith "UnTyped"

let vars = List.init 26 (fun i -> Char.escaped(Char.chr (int_of_char 'a' + i)));;

let multi_char_vars = 
  Seq.(
  append (List.to_seq vars)  
  (concat (List.to_seq vars |> map (fun c -> map (fun x -> c ^ x) (List.to_seq vars))))
)

module StringSet = Set.Make(String);;

let rec collect_vars = function
| Name x -> StringSet.singleton x
| Pair(l, r)
| Application (l, r)
| EvaluationContext((l, _), (r, _) ) -> StringSet.union (collect_vars l) (collect_vars r)
| InjectLeft(_, e) 
| InjectRight(_, e)
| First(e) 
| Second(e)-> (collect_vars e)
| Case (c, (argL, l), (argR, r)) -> StringSet.(
    collect_vars c
    |> union (singleton argL)
    |> union (collect_vars l)
    |> union (singleton argR)
    |> union (collect_vars r)
  )
| _ -> StringSet.empty


let find_unique_var e =
  let names = collect_vars e in
  Option.value ~default:"\\_\\_x" (Seq.find (fun x -> not (StringSet.mem x names)) multi_char_vars)


let rec reduce (e: expr) = 
let open ExprUtils.CurryExpr in
match e with
| Pair(l, r) -> Pair(reduce l, reduce r)
| InjectLeft(l, r) -> InjectLeft(l, reduce r)
| InjectRight(l, r) -> InjectRight(l, reduce r)
| First(Pair(l, _)) -> reduce l
| Second(Pair(_, r)) -> reduce r
| First(e) -> First(reduce e)
| Second(e) -> Second(reduce e)
| Application (Lambda(arg, body), r) -> Translator.substitue arg (reduce r) body
| Application (l, r) -> Application(reduce l, reduce r)
| Case (InjectLeft (_, l), (arg, body), _) -> Translator.substitue arg (reduce l) body
| Case (InjectRight (_, r), _, (arg, body)) -> Translator.substitue arg (reduce r) body
| Case (c, (argL, l), (argR, r)) -> Case(reduce c, (argL, reduce l), (argR, reduce r))
| EvaluationContext((_, et) as c, (Application(CallCC, m), t) ) ->
  (match (is_value m) with 
    | true, _ -> let x = find_unique_var m in
                EvaluationContext(c, ((m @- (x /-> (Abort @- (EvaluationContext (c, (Name x, t)))))), et))
    | false, r -> EvaluationContext(c, (Application(CallCC, r), t))
  )

| EvaluationContext(c, (Application(Control, m), t) ) -> 
  (match (is_value m) with 
    | true, _ ->  let x = find_unique_var m in
                  m @- (x /-> (Abort @- (EvaluationContext (c, (Name x, t)))))
    | false, r -> EvaluationContext(c, (Application(Control, r), t))
  )
| EvaluationContext(c, (Application(Abort, m), t) ) ->
  (match (is_value m) with 
    | true, _ ->  m
    | false, r -> EvaluationContext(c, (Application(Abort, r), t))
  )
| EvaluationContext(a, (e, t) ) -> EvaluationContext(a, (reduce e, t))
| x -> x
and is_value e = let r = reduce e in ((Equality.expr_eq_b e r), r);;