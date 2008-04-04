
open Datatypes
open Autom
open PolyList
open Algo

let rec i2n = function 0 -> O | n -> (S (i2n (pred n)))

let usage () = 
  print_newline (); 
  print_string "The Firing Squad \n";
  print_string "---------------- \n";
  print_string "Automata found by Jacques Mazoyer\n";
  print_string "Coq certification by Jean Duprat\n"; 
  print_string "Code extraction & animation by Pierre Letouzey\n"; 
  print_newline ();
  print_string "Usage:\n" ;
  print_string "./fire <n>      for B&W console\n"; 
  print_string "./fire -c <n>   for colored console (linux only)\n";
  print_string "./fire -x <n>   for graphical window\n";
  print_string "Where <n> is the size of the firing squad\n"; 
  print_newline (); 
  exit 1

type out = BW | Co | X

(********* First Output : Black & White Console ********)

let pr = output_string (Unix.out_channel_of_descr Unix.stdout) 

let bw_of_couleur = function 
  | A -> "A"
  | B -> "B"
  | C -> "C"
  | G -> "G"
  | F -> "F"
  | L -> "L"

let rec bw_print_list = function 
  | Coq_nil -> pr "\n" 
  | Coq_cons (a,l) -> pr (bw_of_couleur a); bw_print_list l

let bw_main n = 
  let l = ref (initial_line O) in  
  bw_print_list !l;
  for i = 1 to 2*n do l:=next_line !l; bw_print_list !l done

(********* Second Output : Colored Console ********)

let c_of_couleur = function 
  | A -> "\027[36mA" 
  | B -> "\027[32mB"
  | C -> "\027[33mC"
  | G -> "\027[34mG"
  | F -> "\027[35mF"
  | L -> "\027[31mL"

let rec c_print_list = function 
  | Coq_nil -> pr "\n" 
  | Coq_cons (a,l) -> pr (c_of_couleur a); c_print_list l

let c_main n = 
  let l = ref (initial_line O) in 
  c_print_list !l;
  for i = 1 to 2*n do l:=next_line !l; c_print_list !l done; 
  pr "\027[0m\n"

(********* Third Output : Graphics ********)

open Graphics

let x_of_couleur = function
  | A -> cyan
  | B -> green
  | C -> yellow
  | G -> blue
  | F -> magenta
  | L -> red
	
let rec x_print_list x y = function 
  | Coq_nil -> ()
  | Coq_cons (a,q) -> set_color (x_of_couleur a); plot x y; x_print_list x (y+1) q

let x_main n = 
  open_graph (Printf.sprintf " %dx%d" (2*n) n);
  let l = ref (initial_line O) in  
  x_print_list 0 0 !l;
  for i = 1 to 2*n do l:=next_line !l; x_print_list i 0 !l done;
  ignore (read_key ())


(************* main **************)

let _ = 
  if Array.length Sys.argv < 2 then usage () 
  else 
    let out, i = 
      if Sys.argv.(1)="-c" then Co, 2
      else if Sys.argv.(1)="-x" then X, 2
      else BW, 1 in 
    let n = try int_of_string Sys.argv.(i) - 1 with _ -> usage () 
    in Nmax.set (i2n n);
    match out with 
      | BW -> bw_main n
      | Co -> c_main n
      | X -> x_main n 






