open Structs

let universalHeader = {|type ('a , 'b) inj = InjL of 'a | InjR of 'b;;

|}

let repeat_tailrec s n =
  let rec helper acc count =
    if count <= 0 then acc
    else helper (acc ^ s) (count - 1)
  in
  helper "" n

let indentStr = repeat_tailrec "    "

let exprToOcaml e =
  let rec inner indent e = match e with
  | Name a -> a
  | TypeUnit -> "()"
  | Pair (l, r) -> Format.asprintf "(%s, %s)" (inner indent l) (inner indent r)
  | First e -> Format.asprintf "(fst %s)" (inner indent e)
  | Second e -> Format.asprintf "(snd %s)" (inner indent e)
  | Application (l, r) -> Format.asprintf "(%s %s)" (inner indent l) (inner indent r)
  | Lambda (x, r) -> Format.asprintf "(fun %s -> %s)" x (inner indent r)
  | InjectLeft (_, x) -> Format.asprintf "(InjL %s)" (inner indent x)
  | InjectRight (_, x) -> Format.asprintf "(InjR %s)" (inner indent x)
  | Case (x, (ln, le), (rn, re)) -> 
    (Format.asprintf "(\n") ^
    (Format.asprintf "%s match %s with\n" (indentStr indent) (inner indent x)) ^
    (Format.asprintf "%s| InjL %s -> %s\n" (indentStr (indent+1)) ln (inner (indent+1) le)) ^
    (Format.asprintf "%s| InjR %s -> %s\n" (indentStr (indent+1)) rn (inner (indent+1) re)) ^
    (Format.asprintf "%s)" (indentStr indent))
  | Abort -> "raise "
  | Bottom -> "Not_found"
  | LetPair (x, y, p, b) -> Format.asprintf "let (%s, %s) = %s in\n%s%s"
    x y (inner (indent+1) p)
    (indentStr indent) (inner (indent+1) b)
  | _ -> "failwith(\"Invalid Source\")"
in universalHeader ^ "let f = " ^ (inner 0 e) ^ ";;"

let wrapMinted s = Format.asprintf {|
\begin{minted}[
    frame=single, %% Adds a frame around the code block
    framesep=2mm, %% Space between frame and code
    linenos, %% Displays line numbers
    fontsize=\small, %% Sets font size
    breaklines %% Allows lines to break if too long
]{ocaml}
%s
\end{minted}
|} s

let wrapVerbatim s = Format.asprintf {|
\begin{verbatim}
%s
\end{verbatim}
|} s

let exprToLatex e = e |> exprToOcaml |> wrapMinted;;