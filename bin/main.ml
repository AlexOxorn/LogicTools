[@@@ warning "-32"];;

let exercise x = print_endline (Format.asprintf "\\section*{Exercise %d}" x)

let same_page x = 
  print_endline "\\begin{samepage}";
  x ();
  print_endline "\\end{samepage}";;


let landscape x = 
  print_endline "\\begin{landscape}";
  List.iter (fun x -> x ()) x;
  print_endline "\\end{landscape}";;


let latex_newpage _ = print_endline "\\newpage";;

let e1 () =
  landscape [
    (fun _ -> exercise 1);
    Logic_tools.Assignments.A4.B1.print;
    Logic_tools.Assignments.A4.B2.print
  ];
  Logic_tools.Assignments.A4.B3.print ();;

let e2 () =
  exercise 2;;

(* A4 *)

let file = Sys.argv.(1);;

match file with
| "B1" -> Logic_tools.Assignments.A4.B1.print ();
| "B2" -> Logic_tools.Assignments.A4.B2.print ();
| "B3" -> Logic_tools.Assignments.A4.B3.print ();
| "B4" -> Logic_tools.Assignments.A4.B4.print ();
| "B5" -> Logic_tools.Assignments.A4.B5.print ();
| "B6" -> Logic_tools.Assignments.A4.B6.print ();
| "B7" -> Logic_tools.Assignments.A4.B7.print ();
| "B8" -> Logic_tools.Assignments.A4.B8.print ();
| "B9" -> Logic_tools.Assignments.A4.B9.print ();
| "B10" -> Logic_tools.Assignments.A4.B10.print ();
| "A1" -> Logic_tools.Assignments.A4.A1.print ();
| "A2" -> failwith "Not implemented yet";
| "A3" -> failwith "Not implemented yet";
| "A4" -> failwith "Not implemented yet";
| "A5" -> failwith "Not implemented yet";
| _ -> Printf.eprintf "Did Not Give File Name\n";;

(* Logic_tools.Assignments.Fun.CurryTransformerTest.print ();

type ('a , 'b) inj = InjL of 'a | InjR of 'b;;

let f = (fun u -> (
match (fst u) with
| InjL a -> (InjL a)
| InjR b -> (
match (snd u) with
| InjL a -> (InjL a)
| InjR c -> (InjR (b, c))
)
));; *)