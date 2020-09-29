(* 
Autore: Giulia De Paola
Data: 2020
Estensione con dizionari dell'interprete didattico in OCAML*)

type ide = string;;
(*evito il passaggio*)
type exp = 
	  Eint of int 
	| Ebool of bool 
	| Den of ide 
	| Prod of exp * exp 
	| Sum of exp * exp 
	| Diff of exp * exp 
	| Eq of exp * exp 
	| Minus of exp 
	| IsZero of exp 
	| Or of exp * exp 
	| And of exp * exp 
	| Not of exp 
	| Ifthenelse of exp * exp * exp 
	| Let of ide * exp * exp 
	| Fun of ide * exp 
	| FunCall of exp * exp 
	| Letrec of ide * exp * exp 
	(*Estensione:
	- Aggiungo dizionario, - possibilità di aggiungere una  nuova coppia o eliminarla,
	- verificare se una chiave è presente in un dizionario, - applicare una funzione ad ogni elem del dict,
	- applicare la funzione sequenzialmente a ogni elemento del dict,
	- Restituire come risultato il dizionario ottenuto dal dizionario d eliminando tutte le coppie chiave-valore 
	per cui la chiave non appartiene alla lista delle chiavi passata come parametro *)
	| EDizionario of dict 
	| Insert of ide * exp * exp 
	| Delete of exp * ide 
	| Has_Key of ide * exp
	| Iterate of exp * exp 
	| Fold of exp * exp 
	| Filter of (ide list) * exp 
	| AccFun of exp * ide * ide   (*Estende funzioni binarie, so già che dovrò associare un valore a quelle stringhe quindi posso scrivere ide al posto di exp*)
	| FunCallAccF of exp * exp * exp 
and dict = Empty | Val of ide * exp * dict
;;
(*Eint è il tipo espressione intera. Ad esempio avrò Eint 6, per avere l'intero 6 chiamo eval Eint 6 e restituisce int 6*)

(*ambiente polimorfo*)
type 't env = ide -> 't;;
let emptyenv (v : 't) = function x -> v;;
let applyenv (r : 't env) (i : ide) = r i;;
let bind (r : 't env) (i : ide) (v : 't) = function x -> if x = i then v else applyenv r x;;

(*tipi esprimibili*)
(*Tipo valutato di cosa*)
type evT = 
	|	Int of int 
	| Bool of bool 
	| Unbound 
	| FunVal of evFun 
	| RecFunVal of ide * evFun
	| ValDict of (ide * evT) list 
	| String of string 
	| ValAccFun of evAccFun (*Chiusura di una funzione che prende un accumulatore*)
and evAccFun = ide * ide * exp * evT env 
and evFun = ide * exp * evT env;;

(*rts*)
(*type checking*)
let rec typecheck (s : string) (v : evT) : bool = (match s with
	|"int" -> (match v with
			Int(_) -> true 
		| _ -> false) 
	|"bool" -> (match v with
		Bool(_) -> true 
		| _ -> false) 
	|"string" -> (match v with
		String(_) -> true 
		|	_ -> false) 
	|"dict" -> (match v with
		| ValDict(_) -> true 
		|_ -> false) 
	|"unbound" -> (match v with
				Unbound -> true
				|_ -> false)
	|"funval" -> (match v with
                FunVal(_) -> true
                | _ -> false)
	|"recfunval"	-> (match v with
                    RecFunVal(_) -> true
                    | _ -> false)
	|"valaccfun" -> (match v with
				ValAccFun(_) -> true
			| _ -> false)
	|"valdict" -> (match v with
					 ValDict(l) -> (match l with
								  	[] -> true
									| (id,x)::xs -> if(typecheck "int" x) then typec "int" (xs)
																	else typec "bool" xs)
					|_ -> false
					)					
	|_ -> failwith("not a valid type"))
	and typec (tp: string) (l:(ide * evT) list) : bool =
			(match l with
			  [] -> true
			| (id,x):: xs -> (typecheck tp x) && (typec tp xs))
;;

(*funzioni primitive*)
(* PRODOTTO *)
let prod x y = if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Int(n*u)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error Prod");;

(* SOMMA *)
let sum x y = 
	if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Int(n+u)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error Sum");;

(* SOTTRAZIONE *)
let diff x y = 
	if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Int(n-u)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error Diff");;

(* UGUAGLIANZA *)
let eq x y = 
	if (typecheck "int" x) && (typecheck "int" y)
		then (match (x,y) with
			(Int(n),Int(u)) -> Bool(n=u)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error eq");;

(* NEGAZIONE *)
let minus x = 
	if (typecheck "int" x) 
		then (match x with
	   		Int(n) -> Int(-n)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error minus");;

(* ISZERO *)
let iszero x = 
	if (typecheck "int" x)
		then (match x with
			Int(n) -> Bool(n=0)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error iszero");;

(* OR *)
let vel x y = 
	if (typecheck "bool" x) && (typecheck "bool" y)
		then (match (x,y) with
			(Bool(b),Bool(e)) -> (Bool(b||e))
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error vel");;

(* AND *)
let et x y = 
	if (typecheck "bool" x) && (typecheck "bool" y)
		then (match (x,y) with
			(Bool(b),Bool(e)) -> Bool(b&&e)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error et");;

(* NOT *)
let non x = 
	if (typecheck "bool" x)
		then (match x with
		  Bool(true) -> Bool(false) 
		| Bool(false) -> Bool(true)
			|_ -> failwith("Typechecking failed"))
	else failwith("Type error not")
;;

(*Funzione ausiliaria per la filter*)
let rec hasK2(k: ide) (keyList: ide list) (r: evT env): bool =
	match keyList with
	 [] -> false
	|x::xs -> if (x=k) then true
				else hasK2 k xs r;;

(*interprete*)
(*Prende un'espressione e l'ambiente di riferimento(che contiene tipi valutati, cioè i val effettivi) e restituise l'espressione valutata

La Fun è la dichiarazione di funzione, lego la funzione (cioè i parametri che usa) all'ambiente dove quei par hanno valore*)
let rec eval (e : exp) (r : evT env) : evT = 
	match e with
	| Eint n -> Int n 
	| Ebool b -> Bool b 
	| IsZero a -> iszero (eval a r) 
	| Den i -> applyenv r i 
	| Eq(a, b) -> eq (eval a r) (eval b r) 
	| Prod(a, b) -> prod (eval a r) (eval b r) 
	| Sum(a, b) -> sum (eval a r) (eval b r) 
	| Diff(a, b) -> diff (eval a r) (eval b r) 
	| Minus a -> minus (eval a r) 
	| And(a, b) -> et (eval a r) (eval b r) 
	| Or(a, b) -> vel (eval a r) (eval b r) 
	| Not a -> non (eval a r) 
	| Ifthenelse(a, b, c) -> 
		let g = (eval a r) in
			if (typecheck "bool" g) 
				then (if g = Bool(true) then (eval b r) else (eval c r))
			else failwith ("nonboolean guard") 
	| Let(i, e1, e2) -> eval e2 (bind r i (eval e1 r)) 
	| Fun(i, a) -> FunVal(i, a, r) 
	| FunCall(f, eArg) -> 
		let fClosure = (eval f r) in
			(match fClosure with
				FunVal(arg, fBody, fDecEnv) -> 
					eval fBody (bind fDecEnv arg (eval eArg r)) |
				RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let aVal = (eval eArg r) in
						let rEnv = (bind fDecEnv g fClosure) in
							let aEnv = (bind rEnv arg aVal) in
								eval fBody aEnv |
				_ -> failwith("non functional value")) 
  | Letrec(f, funDef, letBody) ->
        		(match funDef with
            		Fun(i, fBody) -> let r1 = (bind r f (RecFunVal(f, (i, fBody, r)))) in
                         			                eval letBody r1 |
            		_ -> failwith("non functional def")) 
	| AccFun(f,eArg, acc) -> ValAccFun(eArg, acc, f, r)
  | FunCallAccF(f, eArg, acc) -> let fClosure = (eval f r) in 
    	(match fClosure with
    			ValAccFun(a, param, fBody, fenv) ->
    				let newEnv =(bind fenv param (eval eArg r)) in
    						let nEnv = (bind newEnv a (eval acc r)) in
    									eval fBody nEnv
    			| _->failwith("Invalid function with accumulator"))
  | EDizionario(d) -> ValDict(eval_diz d r)
  | Has_Key(key, where) -> (match (eval where r) with
	    |ValDict(d) -> Bool(has_key key d r)
			|_ ->failwith("Not a dictionary in Has_key"))   
  | Insert(key, value, where) -> (match (eval where r) with 
	    |ValDict(d) -> if(has_key key d r) then failwith("Duplicate key")
						else let v = (eval value r) in ValDict(inserisci key v d r)
			|_ -> failwith("Not a dictionary in Insert"))
  | Delete(where, key) -> (match (eval where r) with
						|ValDict(di) -> if(has_key key di r) then ValDict(delete key di r)
										else failwith("Key not found")
						|_ -> failwith("Not a dictionary in Delete"))
	| Filter(keyList, where) -> (match (eval where r) with
		|ValDict(di) -> ValDict(filter keyList di r)
		|_ -> failwith("Not a dictionary in Filter"))
	| Iterate(f, where) -> ValDict(iterate f where r) 
	| Fold(f, where) -> (match f with
						AccFun _ -> fold f where (Eint(0)) r
						|_-> failwith("Not accumulator function")) 
	and fold (f: exp) (where: exp) (a: exp) (r: evT env): evT =
			(match(eval where r) with
			 |ValDict(di) -> let fClosure = (eval f r) in 
			 let rec aux (d: (ide * evT) list) (ac: evT): evT =
							(match d with
							  [] -> ac
							|(k, v)::ds -> aux ds (evalfunctionacc f v ac r)) 					
			in aux di (eval a r)
			|_-> failwith("Not a dictionary in fold"))
	and evalfunctionacc (f: exp) (eArg: evT) (accumulatore: evT) (r: evT env) : evT = 
	let fClosure = (eval f r) in 
	(match fClosure with
			ValAccFun(a, param, fBody, fenv) ->
				let newEnv =(bind fenv param eArg) in
						let nEnv = (bind newEnv a accumulatore) in
									eval fBody nEnv
			| _->failwith("Invalid function with accumulator"))
	and iterate (f: exp) (where: exp) (r: evT env): (ide * evT) list = 
		(match(eval where r) with 
			|ValDict(di) -> let fClosure = (eval f r) in
			let rec itaux (d: (ide * evT) list): (ide * evT) list = 
					(match d with
					[]-> []
					|(k,v)::ds -> let valore = evalfunction f v r in (k,valore)::itaux(ds))
								in itaux di
			| _ -> failwith("Not a Dictionary")					
		)
	and evalfunction (f: exp) (eArg : evT) (r: evT env) : evT = 
		let fClosure = (eval f r) in
		(match fClosure with
			FunVal(arg, fBody, fDecEnv) -> 
				eval fBody (bind fDecEnv arg eArg) |
			RecFunVal(g, (arg, fBody, fDecEnv)) -> 
					let rEnv = (bind fDecEnv g fClosure) in
						let aEnv = (bind rEnv arg eArg) in
							eval fBody aEnv |
			_ -> failwith("non functional value"))
	and filter (keyList: ide list) (di: (ide * evT) list) (r: evT env): (ide * evT) list =
		(match di with
		 [] -> []
		|(k, v)::ds -> if(hasK2 k keyList r) then (k,v):: filter keyList ds r
						 else filter keyList ds r)
	and delete (key: ide) (di: (ide * evT) list) (r: evT env): (ide * evT) list =
		(match di with
		  [] -> failwith("Key not found")
		| (k,v)::ds -> if(k = key) then ds
						 else [(k, v)]@delete key ds r	
		| _ -> failwith("Error delete"))						 
  and inserisci (key: ide) (v: evT) (di : (ide * evT) list) (r: evT env) : (ide * evT) list=
    	(match di with
    	  [] -> [(key, v)]
			| ds -> [(key, v)]@ds )
   and has_key (key: ide) (di: (ide*evT) list) (r: evT env): bool =
    	(match di with
    	  [] -> false
			|(k, v)::ds -> if(k = key) then true 
										 else has_key key ds r)
   and eval_diz (di: dict) (r: evT env) : (ide * evT) list =
    	(match di with
    	  Empty -> []
			| Val(key,value,ds) -> let v = (eval value r) in if(has_key key (eval_diz ds r) r) then failwith("Duplicate Key")
																											 else (key,v)::eval_diz ds r)
;;
		
(* =============================  TESTS  ============================= *)

let env1 = emptyenv Unbound;; (*Dichiaro nuovo ambiente*)

(* VALUTAZIONE POSITIVA DI UN DIZIONARIO *)
eval (EDizionario(Val("d1",Eint(10),Val("d2",Ebool(true),Empty)))) env1;;

(*GENERAZIONE DI UN ERRORE --> CHIAVE DUPLICATA*)
eval (EDizionario(Val("d1",Eint(10),Val("d1",Ebool(true),Empty)))) env1;;


(* VALUTAZIONE POSITIVA DI UNA HAS_KEY*)
eval (Has_Key("d1",(EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Empty)))))) (emptyenv Unbound);; 


(* VALUTAZIONE POSITIVA DI UNA INSERT*)
eval (Insert("d3",Eint(30),(EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Empty)))))) (emptyenv Unbound);; 

(* INSERISCO (d3,Bool(true))*)
eval (Insert("d3",Ebool(true),(EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Empty)))))) (emptyenv Unbound);; 

(* GENERAZIONE DI UN ERRORE --> CHIAVE DUPLICATA*)
eval (Insert("d3",Eint(30),(EDizionario(Val("d2",Eint(10),Val("d2",Eint(20),Empty)))))) (emptyenv Unbound);; 

(*GENERAZIONE DI UN ERRORE --> CHIAVE DUPLICATA*)
eval (Insert("d3",Eint(30),(EDizionario(Val("d1",Eint(10),Val("d3",Eint(20),Empty)))))) (emptyenv Unbound);; 



(* VALUTAZIONE POSITIVA DI UNA DELETE *)
eval (Delete((EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Val("d3",Eint(30),Empty))))),"d2")) (emptyenv Unbound);; 
(* GENERAZIONE DI UN ERRORE --> CHIAVE NON TROVATA*)
eval (Delete((EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Val("d3",Eint(30),Empty))))),"d4")) (emptyenv Unbound);; 

(*GENERAZIONE DI UN ERRORE --> CHIAVE DUPLICATA*)
eval (Delete((EDizionario(Val("d1",Eint(10),Val("d3",Eint(20),Val("d3",Eint(30),Empty))))),"d4")) (emptyenv Unbound);; 

(*GENERAZIONE DI UN ERRORE--> CHIAVE NON TROVATA*)
eval (Delete(EDizionario(Empty),"d2")) (emptyenv Unbound);; 
 


(* VALUTAZIONE POSITIVA DI UNA FILTER*)
eval (Filter(["d1";"d2"],(EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Val("d3",Eint(30),Empty))))))) (emptyenv Unbound);;


(* VALUTAZIONE POSITIVA DI UNA ITERATE *)
eval (Iterate(Fun("y", Sum(Den "y", Eint 101)),(EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Val("d3",Eint(30),Empty))))))) (emptyenv Unbound);;

eval (Iterate(Fun("y", And(Den "y", Ebool true)),(EDizionario(Val("d1",Ebool(true),Val("d2",Ebool(false),Val("d3",Ebool(true),Empty))))))) (emptyenv Unbound);;


(* VALUTAZIONE POSITIVA DELLA FOLD *)
eval (Fold(AccFun(Sum(Den "acc",Sum(Den "y", Eint 10)),"acc","y"),(EDizionario(Val("d1",Eint(10),Val("d2",Eint(20),Val("d3",Eint(30),Empty))))))) (emptyenv Unbound);;


(* VALUTAZIONE POSITIVA DEL TYPECHECK DINAMICO *)
typecheck "valdict" (eval (EDizionario(Val("d1",Eint(10),Val("d2",Ebool(true),Empty)))) (emptyenv Unbound));;