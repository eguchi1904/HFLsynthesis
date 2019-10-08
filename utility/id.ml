type t =  int
        
let hash :(int, string) Hashtbl.t = Hashtbl.create 1000
let counter = ref 0
            
let genid (s:string) :t =
  let id = !counter in
  (incr counter);
  let str_id = Printf.sprintf "%s.%d" s id in
  let () = Hashtbl.add hash id str_id in
  id

(* 互換性のため *)
let genid_const (s:string) :t =
  let id = !counter in  
  (incr counter);
  let () = Hashtbl.add hash id s in
  id

let valueVar_id = genid_const "_v"


let to_string (t:t) :string=
  match Hashtbl.find_opt hash t with
  |Some str -> str
  |None -> assert false         (* unreachable from outside this module *)

let to_string_readable (t:t) :string=
  match Hashtbl.find_opt hash t with
  |Some str -> str
  |None -> assert false         (* unreachable from outside this module *)         

let to_int t = t



           
