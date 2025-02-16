module Json.Main

open Json.Parser
open Json.Grammar
open FStar.List.Tot

let display_parsed_json (res: option json) : string = 
  match res with
    | None -> "<INVALID JSON>"
    | Some j -> render_json j

let rec read_to_EOF (f: FStar.IO.fd_read) (lines: list string) : FStar.All.ML string = 
  FStar.All.try_with 
    (fun () -> 
      let line = FStar.IO.read_line f in
      read_to_EOF f ([line] @ lines)
    )
    (fun _exn -> (FStar.String.concat "\n" (rev lines)))

// Main program that reads in a file "content.json" in the current directory and emits whether
// the content is valid or invalid JSON.
let main () =
  let f = FStar.IO.open_read_file "content.json" in
  let json = read_to_EOF f [] in
  let parsed_json = parse_json json in
  FStar.IO.close_read_file f; 
  FStar.IO.print_string (display_parsed_json parsed_json)

//Run ``main ()`` when the module loads
#push-options "--warn_error -272"
let _ = main ()