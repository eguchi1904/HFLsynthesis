type e = |App of {head: Id.t;  args: e list}
         |Formula of BaseLogic.t

type condition = |ETermCond of e
                 |PredCond of BaseLogic.t
                         
type b =
  |PIf of (condition * b * b)
  |PMatch of e * (case list)
  |PE of e
 and case =  {constructor : Id.t ;
              argNames : (Id.t * Hfl.baseSort) list ;
              body : b}

type t =
  |PRecFun of Id.t * ((Id.t * Hfl.sort) list) * b

let rec size_e = function
  |Formula _ -> 1
  |App {head = _; args = args} ->
    let args_size =
      List.fold_left
        (fun acc_size arg -> acc_size + (size_e arg))
        0
        args
    in
 args_size + 1
      

let rec to_string_e e =
  match e with
  |Formula formula -> BaseLogic.p2string formula
  |App {head = head; args = args} -> 
    let args_str =
      args
      |> List.map
           (function
            |App {head = arg_head; args = []} ->
              (Id.to_string_readable arg_head)
            | arg -> 
               "("^(to_string_e arg)^")")

      |> String.concat " "
    in
    (Id.to_string_readable head)^" "^args_str

let to_string_cond = function
  |ETermCond e -> to_string_e e
  |PredCond base -> BaseLogic.p2string base
  
let rec to_string_b d b =
  let indent = String.make d ' ' in
  indent^(match b with
          |PIf (cond, b1, b2) ->
            "if "^(to_string_cond cond)^" then\n"
            ^(to_string_b (d+2) b1)
            ^"\n"^indent^"else\n"
            ^(to_string_b (d+2) b2)
          |PMatch (e, cases) ->
            let cases_str =
              List.map (to_string_case (d+2)) cases
              |> String.concat "\n"
            in
            "match "^(to_string_e e)^" with\n"
            ^cases_str

          |PE e -> (to_string_e e)
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
    
              

    
