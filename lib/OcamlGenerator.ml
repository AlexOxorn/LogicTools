open Structs

let universalHeader = {|type ('a , 'b) either = Left of 'a | Right of 'b;;

|}

let repeat_tailrec s n =
  let rec helper acc count =
    if count <= 0 then acc else helper (acc ^ s) (count - 1)
  in
  helper "" n

let indentStr = repeat_tailrec "    "

let exprToOcaml ?(withHeader = false) e =
  let rec combineArgs e =
    match e with
    | Lambda (x, b) ->
        let args, b2 = combineArgs b in
        (x :: args, b2)
    | b -> ([], b)
  in
  let rec inner indent e =
    match e with
    | Name a -> VariableUtils.remove_backslash a
    | TypeUnit -> "()"
    | Pair (l, r) ->
        Format.asprintf "(%s, %s)" (inner indent l) (inner indent r)
    | First e -> Format.asprintf "(fst %s)" (inner indent e)
    | Second e -> Format.asprintf "(snd %s)" (inner indent e)
    | Application (l, r) ->
        Format.asprintf "(%s %s)" (inner indent l) (inner indent r)
    | Lambda _ as ll ->
        let args, b = combineArgs ll in
        Format.asprintf "(fun %s -> %s)"
          (String.concat " " (List.map VariableUtils.remove_backslash args))
          (inner indent b)
    | InjectLeft (_, x) -> Format.asprintf "(Left %s)" (inner indent x)
    | InjectRight (_, x) -> Format.asprintf "(Right %s)" (inner indent x)
    | Case (x, (ln, le), (rn, re)) ->
        Format.asprintf "(\n"
        ^ Format.asprintf "%s match %s with\n" (indentStr indent)
            (inner indent x)
        ^ Format.asprintf "%s| Left %s -> %s\n"
            (indentStr (indent + 1))
            ln
            (inner (indent + 1) le)
        ^ Format.asprintf "%s| Right %s -> %s\n"
            (indentStr (indent + 1))
            rn
            (inner (indent + 1) re)
        ^ Format.asprintf "%s)" (indentStr indent)
    | Abort -> "raise "
    | Bottom -> "Not_found"
    | Let (x, p, b) ->
        Format.asprintf "(let %s = %s in\n%s%s)"
          (VariableUtils.remove_backslash x)
          (inner (indent + 1) p)
          (indentStr indent)
          (inner (indent + 1) b)
    | LetPair (x, y, p, b) ->
        Format.asprintf "(let (%s, %s) = %s in\n%s%s)"
          (VariableUtils.remove_backslash x)
          (VariableUtils.remove_backslash y)
          (inner (indent + 1) p)
          (indentStr indent)
          (inner (indent + 1) b)
    | _ -> "failwith(\"Invalid Source\")"
  in
  if withHeader then universalHeader ^ "let ff = " ^ inner 0 e ^ ";;"
  else inner 0 e

let wrapMinted s =
  Format.asprintf
    {|
\begin{minted}[
    frame=single, %% Adds a frame around the code block
    framesep=2mm, %% Space between frame and code
    linenos, %% Displays line numbers
    fontsize=\small, %% Sets font size
    breaklines %% Allows lines to break if too long
]{ocaml}
%s
\end{minted}
|}
    s

let wrapVerbatim s = Format.asprintf {|\begin{verbatim}
%s
\end{verbatim}|} s

let runCommand ?default inString cmd args =
  let args = Array.of_list args in
  let out, input = Unix.open_process_args cmd args in
  Out_channel.output_string input inString;
  Out_channel.flush input;
  Out_channel.close input;
  (* Unix.sleep(1); *)
  (* Out_channel.close input; *)
  let result = In_channel.input_all out in
  let status = Unix.close_process (out, input) in
  match (default, status) with
  | _, WEXITED 0 -> result
  | Some f, _ -> f
  | _ -> failwith "No Fallback Detected"

let formatOcaml s =
  runCommand ~default:s s "ocamlformat"
    [ "--enable-outside-detected-project"; "--impl"; "-" ]

let getTypeInfoJson s =
  Printf.eprintf
    "single type-expression --filename test.ml -position 1 -expression \"%s\"\n"
    s;
  runCommand ~default:"()" ""
    "/home/alexoxorn/School/Theory1/_opam/bin/ocamlmerlin-server"
    [
      "single type-expression --filename test.ml -position 1 -expression \"" ^ s
      ^ "\"";
    ]

let getOcamlInfo s =
  let s = runCommand (s ^ ";;") "ocaml" [ "-noprompt" ] in
  String.split_on_char '\n' s
  |> List.rev
  |> List.find (fun x -> String.length x > 0)

let clearEmptyLines s =
  String.split_on_char '\n' s
  |> List.filter (fun x -> String.length x > 0)
  |> String.concat "\n"

let extractJsonValue s = runCommand ~default:"()" s "jq" [ "-r"; ".value" ]

let ocamlTypeInference e =
  e |> exprToOcaml |> getOcamlInfo |> clearEmptyLines |> wrapVerbatim

let exprToFormattedOcaml e = e |> exprToOcaml |> formatOcaml |> clearEmptyLines
let exprToLatex e = e |> exprToFormattedOcaml |> wrapMinted
let exprToVerbatim e = e |> exprToFormattedOcaml |> wrapVerbatim

let test =
 fun k0 ->
  k0 (fun u k1 ->
      k1 (fun v k2 ->
          (fun k4 ->
            k4 (fun x alpha k5 ->
                ((fun k6 ->
                   (fun k8 -> x k8) (fun k7 ->
                       (k7 (fun k8 ->
                            k8 (fun y beta k9 -> ((fun k10 -> y k10) alpha) k9)))
                         k6))
                   alpha)
                  k5)) (fun k3 ->
              (k3 (fun k4 ->
                   k4 (fun w k5 ->
                       (fun k7 -> v k7) (fun k6 ->
                           (k6 (fun k7 ->
                                k7 (fun x k8 ->
                                    (fun k10 -> w k10) (fun k9 ->
                                        (k9 (fun k10 ->
                                             (fun k12 -> u k12) (fun k11 ->
                                                 (k11 (fun k12 -> x k12)) k10)))
                                          k8))))
                             k5))))
                k2)))
