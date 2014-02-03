open Ocamlbuild_plugin;;

dispatch 
    (function 
    | After_rules -> dep ["link";"ocaml";"use_z3"] ["src/libz3stubs.a"];
      flag ["link";"ocaml";"use_z3"]
        (S[A"-I";A"src";
           A"-cclib";A"-lz3";
           A"-cclib";A"-lz3stubs";
           A"-cclib";A"-lcamlidl"])
    | _ -> ()
    )
