open Ocamlbuild_plugin
open Unix

let time =
  let tm = Unix.gmtime (Unix.time ()) in
  Printf.sprintf "%02d/%02d/%04d %02d:%02d:%02d UTC"
    (tm.tm_mon + 1) tm.tm_mday (tm.tm_year + 1900)
    tm.tm_hour tm.tm_min tm.tm_sec

let version =
  match run_and_read "git describe --long | tr -d '\\n'" with
  | "" -> "unknown"
  | version -> String.trim version

let ocaml_version =
  match run_and_read "ocamlc -version" with
  | "" -> "unknown"
  | version -> String.trim version

let platform =
  match run_and_read "uname -mpv" with
  | "" -> "unknown"
  | platform -> String.trim platform

let setup_info () =
  let write_version version time platform ocaml_version ch =
    Printf.fprintf ch
      "let version = %S\nlet compile_time = %S\nlet platform = %S\n\
let ocaml_version=%S\n"
      version time platform ocaml_version;
    close_out ch in
  open_out "src/version.ml"
  |> write_version version time platform ocaml_version

let () = dispatch 
    (function
    | After_rules ->
      (* specify [use_z3] tag to annotate 'z3stubs' library as a dependency *)
      dep ["link";"ocaml";"use_z3"] ["src/libz3stubs.a"];
      flag ["link";"ocaml";"use_z3"]
        (S[A"-I";A"src";
           A"-cclib";A"-lz3";
           A"-cclib";A"-lz3stubs";
           A"-cclib";A"-lcamlidl"])
    | After_options ->
      setup_info ()
    | _ -> ()
    )
