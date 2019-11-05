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

type imap = HeadCandidates.t SortM.t
          
type t = smap * imap (* bi directional *)

let smap_to_string smap =
  M.fold
    (fun x sort acc ->
      (Id.to_string_readable x)^":"^(Hfl.sort2string sort)^"; "^acc)
    smap
    ""

let imap_to_string imap =
  SortM.fold
    (fun sort head_candi acc ->
      (Hfl.sort2string (sort:>Hfl.sort))^" -> "^(HeadCandidates.to_string head_candi)
       ^"\n"^acc)
    imap
  ""

let to_string ((smap, imap):t) =
  (smap_to_string smap)^"\n"^(imap_to_string imap)

let empty = (M.empty, SortM.empty)
          

let add_imap sort id (imap:imap) :imap=
  let basesort = Hfl.return_sort  sort in
  let head_candidates = match SortM.find_opt basesort imap with
    |Some head_candidates -> head_candidates
    |None -> HeadCandidates.empty
  in
  (SortM.add basesort (HeadCandidates.add id sort head_candidates) imap)

   
(* let add2imap sort imap = *)
(*   match sort with *)
(*   | Hfl.`FunS _ ->  *)

let add id sort ((smap, imap):t) :t =
  (M.add id sort smap, add_imap sort id imap)
  

let find id ((smap, _):t) :Hfl.sort =
  try M.find id smap
  with Not_found -> invalid_arg "mlEnv.find: not found"

let find_heads base_sort ((_, imap):t) :HeadCandidates.t = 
 SortM.find base_sort imap

  
  

       
