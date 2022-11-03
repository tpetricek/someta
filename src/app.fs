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
  | Apply of Node * Node list
  | Reference of string

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
  | ('_' as c)::input
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
  | TIdent id::TLParen::toks -> parseExprList TComma TRParen (fun args -> 
      Apply(node(Reference(id)), args)) toks
  | TIdent id::toks -> node(Reference(id)), toks
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
  ] in builtin_length(data)
"""

let toks = tokenize [] (List.ofSeq sample)
let e, toks' = parseExpr toks
if toks' <> [] then failwithf "Expected end of expression but got: %A" toks


let (|ExprShape|) e = 
  match e with
  | List(nd) -> "list", nd
  | Tuple(nd) -> "tuple", nd
  | Apply(id, nd) -> $"app(...)", id::nd
  | Primitive(Number n) -> $"number({n})", []
  | Primitive(String s) -> $"string({s})", []
  | Let(id, n1, n2) -> $"let({id})", [n1;n2]
  | Reference(id) -> $"ref({id})", []

let (|ExprEvalChildren|) e = 
  match e with
  | List(nd) -> nd, fun nd -> List nd
  | Tuple(nd) -> nd, fun nd -> Tuple nd
  | Apply(id, nd) -> id::nd, fun nds -> Apply(List.head nds, List.tail nds)
  | Primitive _ | Reference _ -> [], fun _ -> e
  | Let(id, nd, body) -> [nd], fun nds -> 
      Let(id, List.head nds, body)

let rec evalSite orig = 
  match orig.Evaluated with 
  | Some nd when nd.Expression = orig.Expression -> None
  | Some nd -> 
      evalSite nd |> Option.map (fun (es, ctor) ->
        es, fun nnd -> { orig with Evaluated = Some (ctor nnd)})
  | None ->
      let (ExprEvalChildren(children, rebuild)) = orig.Expression
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

let rec substitute v arg nd = 
  if nd.Evaluated.IsSome then failwith "substitute: Cannot subsitutute in evaluated subexpressions"
  match nd.Expression with 
  | Apply(e, es) -> { nd with Expression = Apply(substitute v arg e, List.map (substitute v arg) es) }
  | Let(id, e1, e2) -> { nd with Expression = Let(id, substitute v arg e1, substitute v arg e2) }
  | Reference(id) when id = v -> arg
  | Reference _ | List _ | Tuple _ | Primitive _ -> nd

let rec mostEvalauted nd = 
  match nd.Evaluated with 
  | Some nd -> mostEvalauted nd
  | _ -> nd

let (|MostEvaluated|) nd = mostEvalauted nd

let evalSingle e = 
  match e with 
  | List _ | Tuple _ | Primitive _ -> e
  | Reference id when id.StartsWith("builtin") -> e
  | Reference id -> failwith $"evalSingle: unbound variable {id}"
  | Let(v, arg, body) -> (substitute v arg body).Expression
  | Apply(MostEvaluated { Expression = Reference id }, args) when id.StartsWith "builtin" ->
      let evaldArgs = List.map (fun a -> (mostEvalauted a).Expression) args
      match id, evaldArgs with 
      | "builtin_length", [List els] -> Primitive(Number(float els.Length))
      | _ -> failwith $"evalSingle: Argument mismatch or unsupported operation '{id}'"
  | Apply _ -> failwith "evalSingle: Unsupported application"


let evaluate nd = 
  match evalSite nd with 
  | Some(nd, f) -> f (node (evalSingle nd))
  | None -> nd


type Event = 
  | Toggle of string
  | Evaluate
  | SelectStep of string * int

type State = 
  { Display : Map<string, bool>
    SelectedSteps : Map<string, int>
    Node : Node }

let initial = 
  { Display = Map.empty
    SelectedSteps = Map.empty 
    Node = e } 

let updateUnchecked state evt = 
  match evt with 
  | Toggle id -> 
      let v = Option.defaultValue true (Map.tryFind id state.Display)
      { state with Display = Map.add id (not v) state.Display }
  | SelectStep(id, n) ->
      { state with SelectedSteps = state.SelectedSteps.Add(id, n) }
  | Evaluate ->
      { state with Node = evaluate state.Node }

let update state evt = 
  try updateUnchecked state evt
  with e -> printfn "ERROR: %s" e.Message; state

let rec renderNode state trigger id nd = 
  [ let steps = 
      nd
      |> Seq.unfold (fun st -> Option.map (fun x -> x, x) st.Evaluated) 
      |> Seq.append [nd] |> Array.ofSeq
    let selectedStep = state.SelectedSteps.TryFind id |> Option.defaultValue (steps.Length - 1)
    let selectStep diff _ _ = trigger (SelectStep(id, selectedStep+diff))    
    let (ExprShape(name, children)) = steps.[selectedStep].Expression
    
    if selectedStep > 0 then
      yield h?a [ "href" => "javascript:;"; "click" =!> selectStep (-1) ] [ text " ◀"]
    else yield text " ◀"
    yield h?span [] [ text $" ({selectedStep+1}/{steps.Length})" ]
    if selectedStep < steps.Length - 1 then
      yield h?a [ "href" => "javascript:;"; "click" =!> selectStep (+1) ] [ text " ▶"]
    else yield text " ▶"

    yield text " "
    yield h?a [ 
      "href" => "javascript:;"
      "click" =!> fun _ _ -> trigger (Toggle id) ] [ h?strong [] [ text name] ]

    if children <> [] && Map.tryFind id state.Display = Some false then
      yield text " (...)"
    elif children <> [] then 
      yield h?ul [] [
        for i, c in Seq.indexed children do 
          yield h?li [] (renderNode state trigger $"{id}{i}" c) ]
  ]

let render trigger state = 
  h?div [] [ 
    h?button [ "click"=!> fun _ _ -> trigger Evaluate ] [ text "Evaluate!" ]
    h?ul [] (renderNode state trigger "expr" state.Node)
  ]
    

createVirtualDomApp "app" initial render update
|> ignore