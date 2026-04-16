open PrintLatex
open PrintBeluga

let print_latex_full proof =
  print_string (compact_latex proof);
  print_endline "\\[";
  print_endline (proof_latex proof);
  print_endline "\\]"

let print_seq_latex_full proof =
  print_string (compact_latex proof);
  print_endline "\\[";
  print_endline (seq_proof_latex proof);
  print_endline "\\]"

let print_latex_relation proof1 proof2 =
  print_endline "\\[";
  print_endline (proof_latex proof1);
  print_endline "\\Rightarrow";
  print_endline (proof_latex proof2);
  print_endline "\\]"

let print_multiple_latex f proofs =
  print_endline "\\[";
  print_endline (String.concat " \\quad\\quad " (List.map f proofs));
  print_endline "\\]"

let print_latex_section name e =
  print_endline
    (Format.asprintf "\\subsubsection*{%s: $%s$}" name (expr_latex e))

let print_latex_section2 () =
  print_endline (Format.asprintf "\\subsubsection{}")

let print_beluga proof = print_endline (proof_bel proof)
let print_beluga_with_map map proof = print_endline (proof_bel_base map proof)
let print_beluga_alt proof = print_endline (proof_bel_alt proof)
let print_beluga_seq proof = print_endline (proof_bel_base sym_map_seq proof)

let print_multiple_beluga f proofs =
  print_endline (proofs |> List.map f |> String.concat "\t")

let as_latex prnt proof =
  print_endline "\\begin{verbatim}";
  prnt proof;
  print_endline "\\end{verbatim}"

module type ProofType = sig
  val ctx_separator : string
  val bel_mapping : Structs.inference -> string
  val bel_e_mapping : Structs.expr -> string
  val bel_t_mapping : Structs.ty -> string
end

module NatDed : ProofType = struct
  let ctx_separator = " \\vdash "
  let bel_mapping = sym_map_basic
  let bel_e_mapping _ : string = failwith "Not Implemented"
  let bel_t_mapping _ : string = failwith "Not Implemented"
end

module NatDedCnd : ProofType = struct
  let ctx_separator = " \\vdash "
  let bel_mapping = cnd_mapping
  let bel_e_mapping _ : string = failwith "Not Implemented"
  let bel_t_mapping _ : string = failwith "Not Implemented"
end

module SeqCal : ProofType = struct
  let ctx_separator = " \\implies "
  let bel_mapping = sym_map_seq
  let bel_e_mapping _ : string = failwith "Not Implemented"
  let bel_t_mapping _ : string = failwith "Not Implemented"
end

module CurryCal : ProofType = struct
  let ctx_separator = " \\vdash "
  let bel_mapping = lam_mu_mapping
  let bel_e_mapping = lam_mu_term_mapping
  let bel_t_mapping = lam_mu_type_mapping
end

module BelPrinter (Type : ProofType) = struct
  let symbol_mapping = Type.bel_mapping
  let str = proof_bel_base symbol_mapping

  let stmt (p : Structs.proof) =
    stmtToBel p.con Type.bel_e_mapping ~typeMap:Type.bel_t_mapping p.term

  let full ss n p = Format.asprintf "rec %s: %s\n\t= %s\n;" n (stmt p) (ss p)
  let cat sep ss prfs = String.concat sep (List.map ss prfs)
  let tab ss = cat "\t" ss
  let lf ss = cat "\n" ss
  let space n = cat (String.make n ' ')
  let space4 ss = space 4 ss
  let space8 ss = space 8 ss

  let as_latex strF prf =
    Format.asprintf "\\begin{verbatim}\n%s\n\\end{verbatim}" (strF prf)

  let print strF prf = print_endline (strF prf)
end

module CurryBel = struct
  include BelPrinter (CurryCal)

  let typeOf = curry_bel_proof_base CurryCal.bel_mapping
end

module LatexPrinter (Type : ProofType) = struct
  (* Combinations *)

  let doc_format =
    Format.asprintf
      {|
\documentclass[fleqn]{article}
\usepackage{graphicx} %% Required for inserting images
\usepackage{proof}
\usepackage{geometry}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{xcolor}
\usepackage{minted}
\usepackage{changepage}
\usepackage{pdflscape}
\usepackage{cmll}
\usepackage{arydshln}
\usepackage[bb=boondox]{mathalfa}
\usepackage{fontspec}
\usepackage{fancyvrb} %% Provides enhanced verbatim environments
%% Set a font that supports a wide range of Unicode characters, e.g., DejaVu Sans Mono
\setmonofont{DejaVu Sans Mono}[Scale=MatchLowercase] 

\geometry{paper=letterpaper,left=0.5in,right=0.5in,top=.5in,head=.15in,bottom=0.5in} 
\setlength{\headheight}{5pt}
\def\iamp {\rotatebox[origin=c]{180}{\&}}

\begin{document}
  %s
\end{document}
|}

  let oversized_doc =
    Format.asprintf
      {|
\documentclass[fleqn]{article}
\usepackage{graphicx} %% Required for inserting images
\usepackage{proof}
\usepackage{geometry}
\usepackage{amsmath}
\usepackage{amssymb}
\usepackage{xcolor}
\usepackage{minted}
\usepackage{changepage}
\usepackage{pdflscape}
\usepackage{cmll}
\usepackage{arydshln}
\usepackage[bb=boondox]{mathalfa}
\usepackage{fontspec}
\usepackage{fancyvrb} %% Provides enhanced verbatim environments
%% Set a font that supports a wide range of Unicode characters, e.g., DejaVu Sans Mono
\setmonofont{DejaVu Sans Mono}[Scale=MatchLowercase] 

\geometry{paperwidth=100cm, paperheight=100cm,left=0.5in,right=0.5in,top=.5in,head=.15in,bottom=0.5in} 
\setlength{\headheight}{5pt}
\def\iamp {\rotatebox[origin=c]{180}{\&}}

\begin{document}
  %s
\end{document}
|}

  let wrap_landscape =
    Format.asprintf {|
  \begin{landscape}
  %s
  \end{landscape}
  |}

  let cat sep strF prfs = String.concat sep (List.map strF prfs)
  let quad strF = cat " \\quad " strF
  let qquad strF = cat " \\qquad " strF
  let quad2 strF = cat " \\quad\\quad " strF
  let implies strF = cat " \\Rightarrow " strF
  let hfill strF = cat " \\hfill " strF
  let newline strF = cat "\\newline\\newline" strF

  (* Proofs *)
  let proof = proof_latex_base Type.ctx_separator
  let math strF p = Format.asprintf "\\[\n%s\n\\]" (strF p)

  let math_shrink strF p =
    Format.asprintf
      {|\begin{equation*}
\resizebox{.9\hsize}{!} {
    $%s$
}
\end{equation*}|}
      (strF p)

  let in_math strF p = Format.asprintf "$%s$" (strF p)
  let comp = compact_latex2
  let full p = Format.asprintf "%s\n%s" (comp p) (math proof p)
  let full_fit p = Format.asprintf "%s\n%s" (comp p) (math_shrink proof p)

  let full_mini w p =
    Format.asprintf
      "\\noindent\\begin{minipage}[b]{%f\\textwidth}\n%s%s\n\\end{minipage}" w
      (comp p) (math proof p)

  (* Others *)
  let expr = expr_latex
  let stmt = stmt_latex

  (* Enumeration *)
  let enum s x =
    Format.asprintf "\\begin{enumerate}%s\n\\end{enumerate}"
      (x |> List.map (fun y -> "\\item " ^ s y) |> String.concat "\n")

  let item s x =
    Format.asprintf "\\begin{itemize}%s\n\\end{itemize}"
      (x |> List.map (fun y -> "\\item " ^ s y) |> String.concat "\n")

  let print strF prf = print_endline (strF prf)
end

module NatDedLatex = LatexPrinter (NatDed)
module NatDedBel = BelPrinter (NatDed)
module NatDedCndBel = BelPrinter (NatDedCnd)

(* module CurryBel = BelPrinter (CurryCal) *)
module SeqCalLatex = LatexPrinter (SeqCal)
module SeqCalBel = BelPrinter (SeqCal)
