open MicroCamlTypes
open Utils

exception TypeError of string
exception DeclareError of string
exception DivByZeroError 

(* Provided functions - DO NOT MODIFY *)

(* Adds mapping [x:v] to environment [env] *)
let extend env x v = (x, ref v)::env

(* Returns [v] if [x:v] is a mapping in [env]; uses the
   most recent if multiple mappings for [x] are present *)
let rec lookup env x =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then !value else lookup t x

(* Creates a placeholder mapping for [x] in [env]; needed
   for handling recursive definitions *)
let extend_tmp env x = (x, ref (Int 0))::env

(* Updates the (most recent) mapping in [env] for [x] to [v] *)
let rec update env x v =
  match env with
  | [] -> raise (DeclareError ("Unbound variable " ^ x))
  | (var, value)::t -> if x = var then (value := v) else update t x v
        
(* Part 1: Evaluating expressions *)

(* Evaluates MicroCaml expression [e] in environment [env],
   returning a value, or throwing an exception on error *)
let rec eval_expr env e = match e with
|Value(Int(x)) -> Int(x)
|Value(Bool(x)) -> Bool(x)
|Value(String(x)) -> String(x)
|Value(Closure(x,y,z)) -> Closure(x,y,z)
|ID(x) -> lookup env x
|Fun(v,exp) -> Closure(env,v,exp) 
|Not(exp) -> let exp' = eval_expr env exp in
	(match exp' with
	|Bool(x) -> Bool(not x)
	|_ -> raise (TypeError "No boolean presence"))
|Binop(o,exp1,exp2) -> (match o with
	|Add -> let check_arg1 = eval_expr env exp1 in
		let check_arg2 = eval_expr env exp2 in
		(match check_arg1 with
		|Int(x) -> (match check_arg2 with
			|Int(y) -> Int(x+y)
			|_ -> raise (TypeError "No int for second arguemnt"))
		|_ -> raise (TypeError "No int for first argument"))
	|Sub -> let check_arg1 = eval_expr env exp1 in
		let check_arg2 = eval_expr env exp2 in
		(match check_arg1 with
		|Int(x) -> (match check_arg2 with
			|Int(y) -> Int(x-y)
			|_ -> raise (TypeError "No int for second arguemnt"))
		|_ -> raise (TypeError "No int for first argument"))
	|Mult -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
                |Int(x) -> (match check_arg2 with
                        |Int(y) -> Int(x*y)
                        |_ -> raise (TypeError "No int for second arguemnt"))
                |_ -> raise (TypeError "No int for first argument"))
	|Div -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
                |Int(x) -> (match check_arg2 with
                        |Int(y) -> if y=0 then raise (DivByZeroError) else Int(x/y)
                        |_ -> raise (TypeError "No int for second arguemnt"))
                |_ -> raise (TypeError "No int for first argument"))
	|Greater -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
                |Int(x) -> (match check_arg2 with
                        |Int(y) -> Bool(x>y)
                        |_ -> raise (TypeError "No int for second arguemnt"))
                |_ -> raise (TypeError "No int for first argument"))
	|Less ->let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
                |Int(x) -> (match check_arg2 with
                        |Int(y) -> Bool(x<y)
                        |_ -> raise (TypeError "No int for second arguemnt"))
                |_ -> raise (TypeError "No int for first argument"))
	|GreaterEqual -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
                |Int(x) -> (match check_arg2 with
                        |Int(y) -> Bool(x>=y)
                        |_ -> raise (TypeError "No int for second arguemnt"))
                |_ -> raise (TypeError "No int for first argument"))
	|LessEqual -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
                |Int(x) -> (match check_arg2 with
                        |Int(y) -> Bool(x<=y)
                        |_ -> raise (TypeError "No int for second arguemnt"))
                |_ -> raise (TypeError "No int for first argument"))
	|Concat -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
		|String(x) -> (match check_arg2 with
			|String(y) -> String(x^y)
			|_ -> raise (TypeError "No string in second argument"))
		|_-> raise (TypeError "No string for first argument"))
	|Equal -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
		|String(x) -> (match check_arg2 with
			|String(y)-> Bool(x=y)
			|_ -> raise (TypeError "Unmatching types"))
		|Int(x) -> (match check_arg2 with
			|Int(y) -> Bool(x=y)
			|_-> raise (TypeError "Unmatching types"))
		|Bool(x) -> (match check_arg2 with
			|Bool(y) -> Bool(x=y)
			|_-> raise (TypeError "Unmatching types"))
		|_-> raise (TypeError "Invalid type"))
	|NotEqual -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
                |String(x) -> (match check_arg2 with
                        |String(y)-> Bool(not(x=y))
                        |_ -> raise (TypeError "Unmatching types"))
                |Int(x) -> (match check_arg2 with
                        |Int(y) -> Bool(not(x=y))
                        |_-> raise (TypeError "Unmatching types"))
                |Bool(x) -> (match check_arg2 with
                        |Bool(y) -> Bool(not(x=y))
                        |_-> raise (TypeError "Unmatching types"))
                |_-> raise (TypeError "Invalid type"))
	|Or -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
		|Bool(x) -> (match check_arg2 with
			|Bool(y) -> Bool(x || y)
			|_->raise (TypeError "No boolean type for second arg"))
		|_-> raise (TypeError "No boolean type for first argument"))
	|And -> let check_arg1 = eval_expr env exp1 in
                let check_arg2 = eval_expr env exp2 in
                (match check_arg1 with
		|Bool(x) -> (match check_arg2 with
			|Bool(y) -> Bool(x &&y)
			|_->raise (TypeError "No boolean type for second arg"))
		|_-> raise (TypeError "No boolean type for first arg")))
|If(x,y,z) -> let exp' = eval_expr env x in
	(match exp' with
	|Bool(x) -> if x=true then eval_expr env y else eval_expr env z
	|_ -> raise (TypeError "Guard does not evaluate to boolean"))	
|FunctionCall(exp1,exp2) -> let close = eval_expr env exp1 in
		let exp = eval_expr env exp2 in
		(match close with
		|Closure(x,y,z) -> let a = extend x y exp in eval_expr a z
		|_ -> raise (TypeError "No function closure present"))
|Let(v,b,exp1,exp2) -> if b=true then
			let a = extend_tmp env v in 
			update a v (eval_expr a exp1);
			eval_expr a exp2 
		else
			let a = extend env v (eval_expr env exp1) in
			eval_expr a exp2

(* Part 2: Evaluating mutop directive *)

(* Evaluates MicroCaml mutop directive [m] in environment [env],
   returning a possibly updated environment paired with
   a value option; throws an exception on error *)
let eval_mutop env m = match m with
|Def(v,exp) -> let a = extend_tmp env v in
		update a v (eval_expr a exp);
		(a,Some(eval_expr a exp))
|Expr(e) -> (env,Some(eval_expr env e))
|NoOp -> (env,None)
