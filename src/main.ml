open Core.Std

let run filename =
  let open Term in
  let _ = Term.is_nil_exn Nil in
  ()

let command =
  Command.basic
    ~summary:"Resolve constraints from AstraKahn Term Algebra (AKTA)"
    ~readme:(fun () -> "More detailed information")
    Command.Spec.(
      empty
      +> flag "-dot-output" (optional string) ~doc:"string output network \
        graph in dot format to a file provided as the argument"
      +> anon ("filename" %:string)
    )
    (fun dot_output filename () -> run filename)

let () =
  Command.run ~version:"0.2" ~build_info:"dev version" command

