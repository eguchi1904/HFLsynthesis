type t =  int
        
let hash :(int, (string * (int option))) Hashtbl.t = Hashtbl.create 1000
let counter = ref 0

            
let genid (s:string) :t =
  let id = !counter in
  (incr counter);
  let () = Hashtbl.add hash id (s, Some id) in
  id


let genid_from_id t =
  match Hashtbl.find_opt hash t with
  |Some (s,_) -> genid s
  |None -> assert false         (* unreachable from outside the module *)
         
(* 互換性のため *)
let genid_const (s:string) :t =
  let id = !counter in  
  (incr counter);
  let () = Hashtbl.add hash id (s, None) in
  id

let valueVar_id = genid_const "_v"



let to_string_readable (t:t) :string=
  match Hashtbl.find_opt hash t with
  |Some (str, None) -> str
  |Some (str, Some i) -> str^(string_of_int i)
  |None -> assert false         (* unreachable from outside this module *)
                

let to_string (t:t) :string= to_string_readable t


let to_int t = t

let of_int t = t


let rev_hash: (string, int) Hashtbl.t = Hashtbl.create 1000
(* id refer to string symbol  *)
(* use only in parser *)
let of_string_symbol (s:string) :t =
  match Hashtbl.find_opt rev_hash s with
  |Some i -> i
  |None ->
    let i = !counter in
    (Hashtbl.add rev_hash s i);
    (Hashtbl.add hash i (s, None));
    (incr counter);
    i
    
    
  
