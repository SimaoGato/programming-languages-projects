open Imp

let read_whole_file filename =
    (* open_in_bin works correctly on Unix and Windows *)
    let ch = open_in_bin filename in
    let s = really_input_string ch (in_channel_length ch) in
    close_in ch;
    s

let explode s =
  let rec exp i l =
    if i < 0 then l else exp (i - 1) (s.[i] :: l) in
  exp (String.length s - 1) [];;

let run fuel s =
  let parse_res = parse (explode s) in
  (match parse_res with
    NoneE _ -> print_endline ("Syntax error");
  | SomeE c ->
      match (ceval_step empty_st c [] fuel) with
        Fail ->
          print_endline
            ("Failed!")
      | OutOfGas ->
          print_endline
            ("Still running after " ^ string_of_int fuel ^ " steps")
      | Success (res, _) ->
          print_endline (
            string_of_int (res (explode "res"))))
;;

let usage_msg = "interpreter <file.lpro> [-n interpreter_steps]"
let input_file = ref ""
let interpreter_steps = ref 1000
let anon_fun filename = input_file := filename
let speclist = [
  ("-n", Arg.Set_int interpreter_steps, "Number of steps")
]
let () = Arg.parse speclist anon_fun usage_msg;;
         let argc = Array.length Sys.argv;;
         let () = if argc < 2 then begin
            print_endline usage_msg; exit 0
         end
         let file_contents = (read_whole_file !input_file);;
         run !interpreter_steps file_contents