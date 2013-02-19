let loglevel = ref 3

let logfile = ref stdout

let printf level fmt =
  if level <= !loglevel then
    Printf.fprintf !logfile fmt
  else
    Printf.ifprintf !logfile fmt

let flush () =
  flush !logfile
