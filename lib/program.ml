open Extensions
type term = |App of {head: Id.t;  args: (Id.t * Hfl.sort) list}
            |Formula of BaseLogic.t

(* うーんこの定義が正解かな *)
type e = |Let of (Id.t * Hfl.sort * e * e)
         |Term of term

type b =
  |PIf of (e * b * b)
  |PMatch of e * (case list)
  |PE of e
 and case =  {constructor : Id.t ;
              argNames : (Id.t * Hfl.baseSort) list ;
              body : b}

type t =
  |PRecFun of Id.t * ((Id.t * Hfl.sort) list) * b


(* let の数、closedかつ助長でなければインラン化した時のsize *)
let rec size_e = function
  |Let (_, _, e1, e2) ->
    (size_e e1) + (size_e e2)
  |Term _ -> 1

let rec fv_term = function
  |App {args = args;_} ->
    S.of_list (List.map fst args)
  |Formula e -> BaseLogic.fv_include_v e

let rec fv_term_with_sort = function
  |App {args = args;_} ->
    args
  |Formula e ->
    BaseLogic.fv_sort_include_v e
    |> List.map
         (fun (x, bsort) ->
           (x, ((Hfl.of_baseLogic_sort bsort):> Hfl.sort)))

let rec fv_e_with_sort' = function
  |Term term -> fv_term_with_sort term
  |Let (x, _, e1, e2) ->
    (fv_e_with_sort' e1)@(fv_e_with_sort' e2)
    |> List.filter (fun (x',_) -> x <> x')

let fv_e_with_sort e =
  fv_e_with_sort' e |> List.uniq
    
                       
  
  
  
(* なんか頭が悪いことをしている気がするが...
   BaseLogic.t をe termで使うために
 *)
let rec term_to_string atom_ids str_env term =
  match term with
  |App {head = arg_head; args = []} ->
    (Id.to_string_readable arg_head)
  |App {head = arg_head; args = args} ->
    let args_str =
      List.map
        (fun (arg_id,_) ->
          match M.find_opt arg_id str_env with
          |Some arg_str ->
            if S.mem arg_id atom_ids then
              arg_str
            else
              "("^arg_str^")"
          |None -> "?"^(Id.to_string_readable arg_id))
        args
      |> String.concat " "
    in
    (Id.to_string_readable arg_head)^" "^args_str
  |Formula ((BaseLogic.Var _) as e)->
        let sita = M.mapi
                 (fun _ id_str ->
                   let id_str_id = Id.genid_const id_str in
                   let dummy_sort = BaseLogic.DataS  (Id.genid "dummy", []) in
                    (BaseLogic.Var (dummy_sort, id_str_id))
                 )
                 str_env
    in              
    BaseLogic.p2string (BaseLogic.substitution sita e)

  |Formula e ->
    let sita = M.mapi
                 (fun id id_str ->
                   let id_str = if S.mem id atom_ids then
                                  id_str
                                else
                                  "("^id_str^")"
                   in
                   let id_str_id = Id.genid_const id_str in
                   let dummy_sort = BaseLogic.DataS  (Id.genid "dummy", []) in
                    (BaseLogic.Var (dummy_sort, id_str_id))
                 )
                 str_env
    in              
    BaseLogic.p2string (BaseLogic.substitution sita e)


let is_atom_e e =
  let open BaseLogic in
  match e with
  |Term (App {args = [];_}) -> true
  |Term (Formula (Var _)) -> true
  |_ -> false
                                      

let rec to_string_e_rec atom_ids str_env = function
  |Term term -> term_to_string atom_ids str_env term
  |Let (id, _, e1, e2) ->
    let e1_str = to_string_e_rec atom_ids str_env e1 in
    let str_env = M.add id e1_str str_env in
    let atom_ids =
      if is_atom_e e1 then S.add id atom_ids else atom_ids
    in
    to_string_e_rec atom_ids str_env e2


let to_string_e e =
  to_string_e_rec S.empty M.empty e
    


let term_to_string_direct = function
  |App {head = head; args = args} ->
    let arg_str =
      List.map (fun (x,_) -> Id.to_string_readable  x) args
      |> String.concat " "
    in
    (Id.to_string_readable head)^" "^arg_str
  |Formula e -> BaseLogic.p2string e


              
(* dは開業した時の indent *)
let rec to_string_e_direct d e=
  let indent = String.make d ' ' in
  match e with
  |Let (x,_, e1, e2) ->
    "let "^(Id.to_string_readable x)^" = "
    ^(to_string_e_direct (d+2) e1)^" in \n"^
      indent^(to_string_e_direct d e2)
  |Term term ->
    term_to_string_direct term

    
    
                             
    
  
let rec to_string_b d b =
  let indent = String.make d ' ' in
  indent^(match b with
          |PIf (cond, b1, b2) ->
            "if "^(to_string_e cond)^" then\n"
            ^(to_string_b (d+2) b1)
            ^"\n"^indent^"else\n"
            ^(to_string_b (d+2) b2)
          |PMatch (e, cases) ->
            let cases_str =
              List.map (to_string_case (d+2)) cases
              |> String.concat "\n"
            in
            "match "^(to_string_e  e)^" with\n"
            ^cases_str

          |PE e -> (to_string_e  e)
         )

and to_string_case d {constructor = cons; argNames = args; body = b} =
  let indent = String.make d ' ' in  
  indent^(let args_str =
            args
            |> List.map (fun (x,_) -> (Id.to_string_readable x))
            |> String.concat ","
            |> (fun s-> if List.length args > 1 then "("^s^")"
                        else s)
          in          
          "|"^(Id.to_string_readable cons)^" "^args_str^" ->\n"
          ^(to_string_b (d+2) b)
         )   

let to_string = function
  |PRecFun (name, args, body) ->
    let args_str =
      List.map
        (fun (id, sort) ->
          "("^(Id.to_string_readable id)^":"^(Hfl.sort2string sort)^")")
        args
      |>
        String.concat " "
    in
    "let rec "^(Id.to_string_readable name)^" "^args_str^"=\n"
    ^(to_string_b 2 body)
    
              

    
