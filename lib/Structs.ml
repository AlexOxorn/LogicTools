type expr = 
          (* Nat Deduction *)
          Name of string
          | Top
          | Bottom
          | And of expr * expr
          | NAnd of expr * expr
          | Or of expr * expr
          | Impl of expr * expr
          | Not of expr
          | Nor of expr * expr
          (* Curry Howard *)
          | TypeUnit
          | Pair of expr * expr
          | First of expr
          | Second of expr
          | Application of expr * expr
          | Lambda of string * expr
          | InjectLeft of ty * expr
          | InjectRight of ty * expr
          | Case of expr * (string * expr) * (string * expr)
          (* First Order *)
          | Predicate of string * (expr list)
          | ForAll of string * ty * expr
          | Exists of string * ty * expr
          (* Modal *)
          | Let of string * expr * expr
          | Box of context * expr * judgement
          | CtxExp of context
          (* Linear Logic *)
          | LinOne
          | LinZero
          | LinAndSum of expr * expr
          | LinAndProd of expr * expr
          | LinImpl of expr * expr
          | LinOrSum of expr * expr
          | LinOrProd of expr * expr
          | Bang of expr
          (* Temporal *)
          | NextTime of expr
          (* Continuation *)
          | Control
          | CallCC
          | Abort
          | EvaluationContext of (expr * ty) * (expr * ty)
and ty = NamedType of string
          | NoType
          | UnitType
          | BottomType
          | Sum of (ty * ty)
          | Prod of (ty * ty)
          | Func of (ty * ty)      
and judgement = NoJudge | Truth | TypeOf of ty | Up | Down | Valid
and stmt = { exp : expr; judge : judgement }
and assumption = StmtAssumption of string * stmt
              | VariableAssumption of string * judgement
and context = ConName of string
          | ConApp of context * assumption
          | ConCat of context * context
          | ConNameWithDef of string * context
          | Empty
          | NoContext;;

type inference = 
                (* Axioms *)
                Axiom
                | TopIntro | BottomElim | LinOneElim | LinOneIntro
                | Assumption of string
                | ValidAssumption of string
                | CtxProof
                (* Conjunctions *)
                | AndElimLeft  | PairElimLeft | AndLeft1 of string * string
                | AndElimRight | PairElimRight | AndLeft2 of string * string
                | AndElimAlt of string * string | LinAndProdElim of string * string
                | LetElim of string
                | AndIntro     | PairConstructor | AndRight | LinAndProdIntro  | LinAndSumIntro
                (* Disjunctions *)
                | OrIntroLeft  | VariantIntroLeft | OrRight1
                | OrIntroRight | VariantIntroRight | OrRight2
                | OrElim of string * string | OrLeft of string * string * string
                | VariantElim
                (* Implication *)
                | ImplIntro of string | LambdaIntro of string | ImplRight of string | LinImplIntro of string
                | ImplElim | ApplicationElimination | ImplLeft of string * string | LinImplElim
                (* Negations *)
                | NotIntro of (string * string)
                | NAndIntro of (string * string * string)
                | NorIntro of (string * string * string * string)
                | NotElim
                | NAndElim
                | NorElim1
                | NorElim2
                | ByContra of (string * string)
                (* For All / Exists *)
                | ForAllIntro of string | ForAllRight of string
                | ForAllElim | ForAllLeft of string * string * string
                | ExistsIntro | ExistsRight
                | ExistsElim of string * string | ExistsLeft of string * string * string
                (* Box *)
                | BoxIntro
                | BoxElim of string
                | BangIntro
                | BangElim of string
                | NextIntro
                | NextElim of string
                (* Continuation *)
                | CCIntro
                | CIntro
                | AbortIntro
                | CCElim
                | CElim
                | AbortElim
              ;;

type deductionName = Literal of string
                    | Fancy of string
                    | Subscript of string * string
                    | Substitution of deductionName * ((deductionName * string) list)

type step = Inference of inference * (proof list)
          | Deduction of deductionName
          | NoInference
and
proof = {con: context; term: stmt; inf: step ref};;