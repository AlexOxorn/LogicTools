open Structs
open ContextUtils

let no_judge (x: expr) = {exp=x; judge=NoJudge};;
let is_true (x: expr) = {exp=x; judge=Truth};;
let is_up (x: expr) = {exp=x; judge=Up};;
let is_down (x: expr) = {exp=x; judge=Down};;
let is_valid (x: expr) = {exp=x; judge=Valid};;
let is_type (x: expr) (t: ty) = {exp=x; judge=TypeOf t}

let to_true {exp=x;_} = is_true x;;
let to_no_judge {exp=x;_} = no_judge x;;
let to_valid {exp=x;_} = is_valid x;;

let with_assumption name = Inference(Assumption(name), []);;
let with_valid_assumption name = Inference(ValidAssumption(name), []);;

let _use_assumption assumption_type func con ?st name  = match st with
| Some t -> {con=con; term=func t; inf=ref (assumption_type name)}
| None -> match (Context.lookupStmt name con) with
  | Some t -> {con=con; term=func t; inf=ref (assumption_type name)}
  | None -> failwith "Can't Find Assumption in Context"
;;

let use_assumption = _use_assumption with_assumption Fun.id;;
let use_valid_ass ?(map_judge=to_true) = _use_assumption with_valid_assumption map_judge;;

let make_proof con target rule proofs =
  {con=con; term=target; inf=ref (Inference(rule, proofs))};;
let make_condition con target =
  {con=con; term=target; inf=ref NoInference};;
let make_deduction con target deduction = {con=con; term=target; inf=ref (Deduction deduction)};;

let (?@) s = (Literal s);;
let (?$) s = (Fancy s);;
let (^>) s x = (Subscript (s, x));;





let make_implication a b = Inference(ImplElim, [a; b]);;