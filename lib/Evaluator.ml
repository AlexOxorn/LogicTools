open Structs;;
open ExprUtils.CurryExpr;;

let stmt_to_exp_ty = function
| {exp=e; judge=TypeOf t} -> e, t
| _ -> failwith "UnTyped"

let reduce (e: expr) = match e with
| First(Pair(l, _)) -> l
| Second(Pair(_, r)) -> r
| Application (Lambda(arg, body), r) -> Translator.substitue arg r body
| Case (InjectLeft (_, l), (arg, body), _) -> Translator.substitue arg l body
| Case (InjectRight (_, r), _, (arg, body)) -> Translator.substitue arg r body
| EvaluationContext((_, et) as c, (Application(CallCC, m), t) ) -> 
    EvaluationContext(c, ((m @- ("x" /-> (EvaluationContext (c, (Name "x", t))))), et))
| EvaluationContext(c, (Application(Control, m), t) ) -> 
    m @- ("x" /-> (EvaluationContext (c, (Name "x", t))))
| EvaluationContext(_, (Application(Abort, m), _) ) -> m
| x -> x