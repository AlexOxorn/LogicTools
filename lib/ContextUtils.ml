open Structs
module StmtMap = Map.Make (String)

type _strMap = string -> string

module type ContextFunctions = sig
  type t = context
  type ass = assumption
  type flags

  val empty : t
  val add : ?alt:flags -> string -> stmt -> t -> t
  val add_var : ?alt:flags -> string -> judgement -> t -> t
  val name : string -> ?alt:flags -> t -> t
  val cat : t -> t -> t
  val remove_by : (ass -> bool) -> ?ctxMap:(string -> string) -> t -> t
  val remove_name : string -> ?ctxMap:(string -> string) -> t -> t
  val transform_by : (ass -> bool) -> (ass -> ass) -> t -> t
  val transform_all : (ass -> ass) -> t -> t
  val remove_ctx_name : string -> ?ctxMap:(string -> string) -> t -> t
  val lookupAss : string -> t -> ass option
  val lookupStmt : string -> t -> stmt option
  val findStmt : (assumption -> bool) -> t -> stmt option
  val findAss : (assumption -> bool) -> t -> ass option
  val extract : ?ctxMap:(string -> string) -> t -> t -> t

  val extract_names :
    ?leftName:string -> ?rightName:string -> string list -> t -> t * t

  val collapse : t -> t
  val equal : t -> t -> bool
  val equivalent : t -> t -> bool
  val latex : (ass -> string) -> t -> string
  val toMap : t -> stmt StmtMap.t
  val reifyContext : t -> t
  val flatten : t -> assumption list
end

module Context : ContextFunctions = struct
  type t = context
  type ass = assumption
  type flags = unit

  let empty = Empty

  let _getname = function
    | StmtAssumption (n, _) | VariableAssumption (n, _) -> n

  let _assToStmt = function
    | StmtAssumption (_, x) -> x
    | VariableAssumption (n, j) -> { exp = Name n; judge = j }

  let add ?alt:_ name st con = ConApp (con, StmtAssumption (name, st))
  let add_var ?alt:_ name jd con = ConApp (con, VariableAssumption (name, jd))
  let name name ?alt:_ con = ConNameWithDef (name, con)
  let cat c2 c1 = ConCat (c1, c2)

  let remove_by pred ?ctxMap con =
    let rec inner pred ctxMap con =
      match con with
      | ConName _ | Empty | NoContext -> (con, false)
      | ConApp (c, a) ->
          let newC, p = inner pred ctxMap c in
          if pred a then (newC, true) else (ConApp (newC, a), p)
      | ConCat (c1, c2) ->
          let s1, p1 = inner pred ctxMap c1 in
          let s2, p2 = inner pred ctxMap c2 in
          (ConCat (s1, s2), p1 || p2)
      | ConNameWithDef (x, c) ->
          let sub, p = inner pred ctxMap c in
          if p then
            match ctxMap with
            | Some f -> (ConNameWithDef (f x, sub), p)
            | None -> (sub, p)
          else (ConNameWithDef (x, sub), p)
    in
    fst (inner pred ctxMap con)

  let remove_name n = remove_by (fun x -> n = _getname x)

  let rec transform_by pred func con =
    match con with
    | ConName _ | Empty | NoContext -> con
    | ConApp (c, a) ->
        let newC = transform_by pred func c in
        if pred a then ConApp (newC, func a) else ConApp (newC, a)
    | ConCat (c1, c2) ->
        ConCat (transform_by pred func c1, transform_by pred func c2)
    | ConNameWithDef (x, c) -> ConNameWithDef (x, transform_by pred func c)

  let transform_all = transform_by (fun _ -> true)

  let rec _find pred post con =
    match con with
    | ConName _ | Empty | NoContext -> None
    | ConApp (c, a) -> if pred a then Some (post a) else _find pred post c
    | ConCat (c1, c2) ->
        let lhs = _find pred post c1 in
        if Option.is_some lhs then lhs else _find pred post c2
    | ConNameWithDef (_, c) -> _find pred post c

  let findAss pred con = _find pred Fun.id con
  let findStmt pred = _find pred _assToStmt
  let lookupAss n = findAss (fun a -> n = _getname a)
  let lookupStmt n = findStmt (fun a -> n = _getname a)

  let collapse con =
    let rec collapse_step context =
      match context with
      | ConNameWithDef (_, ConNameWithDef (x, c)) -> ConNameWithDef (x, c)
      | ConNameWithDef (_, Empty) -> Empty
      | ConNameWithDef (x, y) -> ConNameWithDef (x, collapse_step y)
      | ConApp (c, s) -> ConApp (collapse_step c, s)
      | ConCat (Empty, Empty) -> Empty
      | ConCat (Empty, c) | ConCat (c, Empty) -> c
      | ConCat (c1, c2) -> ConCat (collapse_step c1, collapse_step c2)
      | _ -> context
    in
    let res = collapse_step con in
    if Equality.context_strict_equal_b res con then res else collapse_step res

  let toMap c =
    let rec inner m c =
      match c with
      | NoContext | Empty | ConName _ -> m
      | ConApp (c, a) -> inner (StmtMap.add (_getname a) (_assToStmt a) m) c
      | ConCat (l, r) ->
          StmtMap.union (fun _ a _ -> Some a) (inner m l) (inner m r)
      | ConNameWithDef (_, c) -> inner m c
    in
    inner StmtMap.empty c

  let rec equal (l : context) (r : context) =
    match (l, r) with
    | ConName a, ConName b -> a = b
    | ConApp (c1, a1), ConApp (c2, a2) ->
        Equality.assumption_eq_b a1 a2 && equal c1 c2
    | ConCat (c1, a1), ConCat (c2, a2) -> equal a1 a2 && equal c1 c2
    | ConNameWithDef (n1, c1), ConNameWithDef (n2, c2) ->
        n1 == n2 && equal c1 c2
    | Empty, Empty | NoContext, NoContext -> true
    | ConNameWithDef (_, c1), x | x, ConNameWithDef (_, c1) -> equal c1 x
    | _ -> false

  let equivalent (l : context) (r : context) =
    StmtMap.equal ( = ) (toMap l) (toMap r)

  let rec latex assPrinter ctx =
    match ctx with
    | Empty -> "\\,\\cdot\\,"
    | ConName a -> a
    | ConApp (Empty, r) -> Format.asprintf "%s" (assPrinter r)
    | ConApp (l, r) ->
        Format.asprintf "%s,\\ %s" (latex assPrinter l) (assPrinter r)
    | ConCat (l, r) ->
        Format.asprintf "%s,\\ %s" (latex assPrinter l) (latex assPrinter r)
    | ConNameWithDef (n, _) -> n
    | NoContext -> ""

  let remove_ctx_name pred ?ctxMap con =
    let rec inner pred ctxMap con =
      match con with
      | Empty | NoContext -> (con, false)
      | ConApp (c, a) ->
          let sub, p = inner pred ctxMap c in
          (ConApp (sub, a), p)
      | ConCat (c1, c2) ->
          let s1, p1 = inner pred ctxMap c1 in
          let s2, p2 = inner pred ctxMap c2 in
          (ConCat (s1, s2), p1 || p2)
      | ConName n -> if pred = n then (Empty, true) else (con, false)
      | ConNameWithDef (x, c) ->
          if pred = x then (Empty, true)
          else
            let sub, p = inner pred ctxMap c in
            if p then
              match ctxMap with
              | Some f -> (ConNameWithDef (f x, sub), p)
              | None -> (sub, p)
            else (ConNameWithDef (x, sub), p)
    in
    fst (inner pred ctxMap con)

  let rec extract ?ctxMap (ref : t) (self : t) =
    match ref with
    | NoContext | Empty -> self
    | ConName n -> remove_ctx_name ?ctxMap n self
    | ConApp (c, a) ->
        let b = extract ?ctxMap c self in
        remove_by (Equality.assumption_eq_b a) ?ctxMap b
    | ConCat (l, r) ->
        let b = extract ?ctxMap l self in
        extract ?ctxMap r b
    | ConNameWithDef (x, d) ->
        let p = remove_ctx_name ?ctxMap x self in
        extract ?ctxMap d p

  let extract_names ?leftName ?rightName (names : string list) (self : t) =
    let rec inner (names : string list) (self : t) =
      match self with
      | NoContext | ConName _ | Empty -> (Empty, self)
      | ConApp (c, (VariableAssumption (s, _) as a))
      | ConApp (c, (StmtAssumption (s, _) as a)) ->
          let l, r = inner names c in
          if List.mem s names then (ConApp (l, a), r) else (l, ConApp (r, a))
      | ConCat (l, r) ->
          let l1, r1 = inner names l in
          let l2, r2 = inner names r in
          (ConCat (l1, l2), ConCat (r1, r2))
      | ConNameWithDef (_, d) -> inner names d
    in
    let c1, c2 = inner names self in
    match (leftName, rightName) with
    | Some x, Some y -> (name x c1, name y c2)
    | Some x, None -> (name x c1, c2)
    | None, Some y -> (c1, name y c2)
    | None, None -> (c1, c2)

  let reifyContext = function NoContext -> empty | c -> c

  let rec flatten = function
    | Empty -> []
    | ConApp (c, a) -> flatten c @ [ a ]
    | ConCat (l, r) -> flatten l @ flatten r
    | ConNameWithDef (_, c) -> flatten c
    | _ -> failwith "Contexts need to be Fully Defined"
end

module ModalContext = struct
  include Context

  type flags = HypCTX | ValidCTX | Auto

  let empty = ConCat (Empty, Empty)

  let add ?(alt = Auto) n s c =
    match (alt, c, s) with
    | Auto, ConCat (l, r), { judge = Valid; _ } | ValidCTX, ConCat (l, r), _ ->
        ConCat (Context.add n s l, r)
    | Auto, ConCat (l, r), _ | HypCTX, ConCat (l, r), _ ->
        ConCat (l, Context.add n s r)
    | _ -> failwith "Modal Context Must Have Top-level Context Concatenation"

  let add_var ?alt:_ n s c =
    match (c, s) with
    | ConCat (l, r), Valid -> ConCat (Context.add_var n s l, r)
    | ConCat (l, r), _ -> ConCat (l, Context.add_var n s r)
    | _ -> failwith "Modal Context Must Have Top-level Context Concatenate"

  let nameLeft n c =
    match c with
    | ConCat (l, r) -> ConCat (Context.name n l, r)
    | _ -> failwith "Modal Context Must Have Top-level Context Concatenate"

  let nameRight n c =
    match c with
    | ConCat (l, r) -> ConCat (l, Context.name n r)
    | _ -> failwith "Modal Context Must Have Top-level Context Concatenate"

  let name n ?(alt = HypCTX) =
    match alt with ValidCTX -> nameLeft n | HypCTX | Auto -> nameRight n

  let cat _ _ = failwith "Can't Concatenate Combined Modal Context"

  let collapse = function
    | ConCat (l, r) -> ConCat (Context.collapse l, Context.collapse r)
    | c -> Context.collapse c

  let latex assPrinter ctx =
    match ctx with
    | ConCat (l, r) ->
        Format.asprintf "%s;\\ %s"
          (Context.latex assPrinter l)
          (Context.latex assPrinter r)
    | _ -> failwith "Modal Context Must Have Top-level Context Concatenate"

  let extract_names ?leftName ?rightName names c =
    match c with
    | ConCat (l, r) ->
        let c1, c2 = Context.extract_names ?leftName ?rightName names r in
        (ConCat (l, c1), ConCat (l, c2))
    | _ -> failwith "Modal Context Must Have Top-level Context Concatenate"
end

module TemporalContext = struct
  include Context

  [@@@warning "-37"]

  type flags = CurrCTX | NextCTX

  [@@@warning "+37"]

  let empty = ConCat (Empty, Empty)

  let _split = function
    | ConCat (a, b) -> (a, b)
    | _ -> failwith "Temporal Context Must Have Top-level Context Concatenation"

  let next x =
    let l, _ = _split x in
    ConCat (Empty, l)

  let add ?(alt = CurrCTX) n s c =
    let l, r = _split c in
    match alt with
    | NextCTX -> ConCat (Context.add n s l, r)
    | CurrCTX -> ConCat (l, Context.add n s r)

  let add_var ?(alt = CurrCTX) n s c =
    let l, r = _split c in
    match alt with
    | NextCTX -> ConCat (Context.add_var n s l, r)
    | CurrCTX -> ConCat (l, Context.add_var n s r)

  let nameLeft n c =
    match c with
    | ConCat (l, r) -> ConCat (Context.name n l, r)
    | _ -> failwith "Temporal Context Must Have Top-level Context Concatenate"

  let nameRight n c =
    match c with
    | ConCat (l, r) -> ConCat (l, Context.name n r)
    | _ -> failwith "Temporal Context Must Have Top-level Context Concatenate"

  let name n ?(alt = CurrCTX) =
    match alt with NextCTX -> nameLeft n | CurrCTX -> nameRight n

  let cat _ _ = failwith "Can't Concatenate Combined Modal Context"

  let collapse = function
    | ConCat (l, r) -> ConCat (Context.collapse l, Context.collapse r)
    | c -> Context.collapse c

  let latex assPrinter ctx =
    match ctx with
    | ConCat (l, r) ->
        Format.asprintf "%s;\\ %s"
          (Context.latex assPrinter l)
          (Context.latex assPrinter r)
    | _ -> failwith "Temporal Context Must Have Top-level Context Concatenate"
end
