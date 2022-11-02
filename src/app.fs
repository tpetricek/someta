module App
open Tbd.Html

type Primitive =
  | Number of float
  | String of string

type Node = 
  { Expression : Expr
    Evaluated : Node option }

and Expr = 
  | List of Node list
  | Tuple of Node list
  | Primitive of Primitive
  | Let of string * Node * Node

let node e = { Expression = e; Evaluated = None }


type Token = 
  | TEquals
  | TLet | TIn
  | TComma | TSemicolon
  | TLBrack | TRBrack | TLParen | TRParen
  | TIdent of string
  | TNumber of float

let toString c = System.String(Array.ofList c)

let (|PLetter|_|) c = 
  if System.Char.IsLetter(c) then Some(c) else None

let (|PNumber|_|) c = 
  if System.Char.IsNumber(c) then Some(c) else None

let (|PWhite|_|) input =
  match input with 
  | ' '::input -> Some input
  | '\r'::input -> Some input
  | '\n'::input -> Some input
  | _ -> None

let (|PWhiteOrEnd|_|) input =
  match input with 
  | PWhite input -> Some input
  | [] -> Some []
  | _ -> None

let (|PStartsWith|_|) prefix input = 
  let rec loop prefix input = 
    match input, prefix with 
    | input, [] -> Some(input)
    | i::is, p::ps when i = p -> loop ps is
    | _ -> None
  loop (List.ofSeq prefix) input

let ops = 
  dict [ ';', TSemicolon; ',', TComma; '(', TLParen; ')', TRParen; 
         '[', TLBrack; ']', TRBrack; '=', TEquals ]

let rec tokenizeIdent acc iacc input = 
  match input with 
  | PLetter c::input -> tokenizeIdent acc (c::iacc) input
  | _ -> tokenize (TIdent(toString (List.rev iacc))::acc) input

and tokenizeNumber acc iacc input = 
  match input with 
  | (PNumber c | ('.' & c))::input -> tokenizeNumber acc (c::iacc) input
  | _ -> tokenize (TNumber(float (toString (List.rev iacc)))::acc) input

and tokenize acc input =
  match input with 
  | [] -> List.rev acc
  | c::input when ops.ContainsKey c -> tokenize (ops.[c]::acc) input
  | PStartsWith "let" (PWhiteOrEnd input) -> tokenize (TLet::acc) input
  | PStartsWith "in" (PWhiteOrEnd input) -> tokenize (TIn::acc) input
  | PLetter c::input -> tokenizeIdent acc [c] input
  | PNumber c::input -> tokenizeNumber acc [c] input
  | PWhite input -> tokenize acc input
  | input -> failwithf "Unexpected input: %A" input

let rec parseExprList tsep tend ctor toks = 
  let rec loop acc toks = 
    match parseExpr toks with
    | e, ts::toks when ts = tsep -> loop (e::acc) toks
    | e, ts::toks when ts = tend -> node(ctor(List.rev (e::acc))), toks
    | _, toks -> failwithf "parseExprList: Expected '%A' or '%A' but got %A" tsep tend toks
  loop [] toks

and parseExpr toks = 
  match toks with 
  | TLBrack::toks -> parseExprList TSemicolon TRBrack List toks
  | TLParen::toks -> parseExprList TComma TRParen Tuple toks
  | TNumber n::toks -> node(Primitive(Number n)), toks
  | TLet::TIdent id::TEquals::toks -> 
      match parseExpr toks with 
      | ea, TIn::toks -> 
          let eb, toks = parseExpr toks
          node(Let(id, ea, eb)), toks
      | ea, toks -> failwithf "parseExpr: Expected 'in' but got %A" toks
  | toks -> failwithf "parseExpr: Unexpected %A" toks

let sample = """
  let data = [
    (2013, 12.3);
    (2014, 56.7)
  ] in 1
"""

let toks = tokenize [] (List.ofSeq sample)
let e, toks' = parseExpr toks
if toks' <> [] then failwithf "Expected end of expression but got: %A" toks


let (|ExprShape|) e = 
  match e with
  | List(nd) -> "list", nd, fun nd -> List nd
  | Tuple(nd) -> "tuple", nd, fun nd -> Tuple nd
  | Primitive(Number n) -> $"number({n})", [], fun _ -> e
  | Primitive(String s) -> $"string({s})", [], fun _ -> e
  | Let(id, n1, n2) -> $"let({id})", [n1;n2], fun nd -> 
      Let(id, List.item 0 nd, List.item 1 nd)

      (*
let evaluateExpr e = 
  printfn "Evaluating: %A" e
  match e with 
  | Primitive p -> Primitive p
  //| List of Node list
  //| Tuple of Node list
  //| Let of string * Node * Node
  | _ -> e

let rec evaluate nd = 
  match nd.Evaluated with 
  | Some nde -> 
      { nd with Evaluated = Some (evaluate nde) }
  | None -> 
      let (ExprShape(_, children, ctor)) = nd.Expression
  if children |> List.forall (fun c -> c.Evaluated.IsSome) then 
    { nd with Evaluated = Some (node (evaluateExpr nd.Expression)) }
  else 
    //let eval, unev = children |> List.partition (fun c -> c.Evaluated.IsSome)
    nd //{ nd with Evaluated = Some (ctor (eval @ [ evaluate (List.head unev) ] @ List.tail unev))}
    &*)

let rec evalSite orig = 
  match orig.Evaluated with 
  | Some nd when nd.Expression = orig.Expression -> None
  | Some nd -> 
      evalSite nd |> Option.map (fun (es, ctor) ->
        es, fun nnd -> { orig with Evaluated = Some (ctor nnd)})
  | None ->
      let (ExprShape(_, children, rebuild)) = orig.Expression
      let rec childEvalSite skipped = function
        | c::cs -> 
            match evalSite c with 
            | None -> childEvalSite (c::skipped) cs
            | Some(es, ctor) -> 
                Some(es, fun nnd -> { orig with Evaluated = Some(node(rebuild ((List.rev skipped) @ (ctor nnd)::cs))) })
        | [] -> None
      match childEvalSite [] children with 
      | None -> Some(orig.Expression, fun nnd -> { orig with Evaluated = Some(nnd) })
      | Some es -> Some es

let evaluate nd = 
  match evalSite nd with 
  | Some(nd, f) -> 
      //printfn "Eval: %A" nd
      //printfn "Returns: %A" (f (node nd))
      f (node nd)
  | None -> nd


type Event = 
  | Toggle of string
  | Evaluate

type State = 
  { Display : Map<string, bool>
    Node : Node }

let initial = 
  { Display = Map.empty
    Node = e } 

let update state evt = 
  match evt with 
  | Toggle id -> 
      let v = Option.defaultValue true (Map.tryFind id state.Display)
      { state with Display = Map.add id (not v) state.Display }
  | Evaluate ->
      { state with Node = evaluate state.Node }

let rec renderNode state trigger id nd = 
  let (ExprShape(name, children, _)) = nd.Expression   
  let table c c1 c2 = 
    [ h?div [ "class"=>c ] [ 
        h?div ["class"=>"ndexpr"] c1;
        h?div ["class"=>"ndeval"] c2 ] ]
  table (if nd.Evaluated.IsSome then "ndcontv" else "ndconth")
    [ yield h?a [ 
        "href" => "javascript:;"
        "click" =!> fun _ _ -> trigger (Toggle id) ] [text name]
      if nd.Evaluated.IsSome then 
        yield text " (source)" 
      elif children <> [] && Map.tryFind id state.Display = Some false then
        yield text " (...)"
      elif children <> [] then 
        yield h?ul [] [
          for i, c in Seq.indexed children do 
            yield h?li [] (renderNode state trigger $"{id}{i}" c) ]
    ] (
      match nd.Evaluated with 
      | None -> [ text "(unevaluated)" ]
      | Some nd -> renderNode state trigger $"{id}e" nd
    )


let render trigger state = 
  h?div [] [ 
    h?button [ "click"=!> fun _ _ -> trigger Evaluate ] [ text "Evaluate!" ]
    h?ul [] (renderNode state trigger "expr" state.Node)
  ]
    

createVirtualDomApp "app" initial render update
|> ignore