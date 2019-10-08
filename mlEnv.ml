module SortM =
  struct
    module SortM = (Map.Make
                      (struct
                        type t = Hfl.baseSort
                        let compare = compare
                      end)
                   )
    include SortM
          
    let add_list_map key elm (map: ('a list) t) =
      if SortM.mem key map then
        (SortM.add key (elm :: (SortM.find key map)) map)
      else
        SortM.add key [elm] map
  end

type smap = Hfl.sort M.t
type imap = ((Id.t * Hfl.sort) list) SortM.t
          
type t = smap * imap (* bi directional *)

       let empty = (M.empty, SortM.empty)
(* アリティ0のものがリストの先頭に来るように *)
let rec insert_id_sort_list id sort l =
  match l with
  |[] -> [(id,sort)]
  |(id', sort')::xs ->
    if Hfl.is_baseSort sort || not (Hfl.is_baseSort sort') then
      (id, sort)::l
    else
      (id', sort')::(insert_id_sort_list id sort xs)


let add_imap sort id (imap:imap) :imap=
  let basesort = Hfl.return_sort  sort in
  if SortM.mem basesort imap then
    let id_sort_list = SortM.find basesort imap in
    (SortM.add basesort (insert_id_sort_list id sort id_sort_list) imap)
  else
    SortM.add basesort [(id, sort)] imap
   
(* let add2imap sort imap = *)
(*   match sort with *)
(*   | Hfl.`FunS _ ->  *)

let add id sort ((smap, imap):t) :t =
  (M.add id sort smap, add_imap sort id imap)

let find id ((smap, _):t) :Hfl.sort =
  try M.find id smap
  with Not_found -> invalid_arg "mlEnv.find: not found"

let find_heads base_sort ((_, imap):t) :(Id.t * Hfl.sort) list =
  SortM.find base_sort imap

  
  

       
