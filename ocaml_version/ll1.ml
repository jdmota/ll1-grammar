(* Utils *)

module SS = Set.Make(String);;

let rec foreach array fn =
	match array with
	| [] -> ()
	| v::array -> fn v; foreach array fn;;

let rec reduce x list fn =
  match list with
  | [] -> x
  | v::array -> fn v (reduce x array fn);;

let rec mapConcat array fn =
	match array with
	| [] -> []
	| v::array -> fn v @ mapConcat array fn;;

let rec indexOf2 el array startIdx =
	match array with
	| [] -> -1
	| el2::array -> if el = el2 then startIdx else indexOf2 el array (startIdx + 1);;

let indexOf el array = indexOf2 el array 0;;

let rec slice array idx =
	match array with
	| [] -> []
	| v::rest -> if idx = 0 then array else slice rest (idx-1);;

(* LL1 *)

exception NotDeterministic of string;;
exception LeftRecursive of string;;

type rule = { name: string; rightside: string list };;
type grammar = { rulesByName: ( string * rule list ) list; rules: rule list; nonTerminals: SS.t };;

let isTerminal variable grammar = SS.mem variable grammar.nonTerminals = false;;

let getRules variable rulesByName = let (_, b) = List.find (fun (a, b) -> a = variable) rulesByName in b;;

let rec canBeEmpty variables grammar =
	List.for_all (fun var -> canBeEmptyVariable var grammar) variables

and canBeEmptyVariable variable grammar =
	if isTerminal variable grammar then false else
		let rules = getRules variable grammar.rulesByName in List.exists (fun rule -> canBeEmpty rule.rightside grammar) rules;;

let rec first2 variables set grammar =
	match variables with
	| [] -> []
	| variable::rest -> if isTerminal variable grammar then variable::[] else firstRest rest set grammar @ firstVariable variable set grammar

and firstRest variables set grammar=
	if canBeEmpty variables grammar then first2 variables set grammar else []

and firstVariable variable set grammar =
	if SS.mem variable set then raise (LeftRecursive variable) else mapConcat (getRules variable grammar.rulesByName) (fun rule -> first2 rule.rightside (SS.add variable set) grammar);;

let first variables grammar = first2 variables SS.empty grammar;;
		
let whereItShows variable grammar = reduce [] grammar.rules (fun rule result ->
	let i = indexOf variable rule.rightside in if i = 0 - 1 then result else (rule, slice rule.rightside (i + 1))::result
);;

let rec follow variable grammar =
	mapConcat (whereItShows variable grammar) (fun (rule, next) -> first next grammar @ (if canBeEmpty next grammar then follow rule.name grammar else []) );;

let lookahead rule grammar =
	(if canBeEmpty rule.rightside grammar then follow rule.name grammar else []) @ first rule.rightside grammar;;

let join set array = reduce set array (fun v set -> if SS.mem v set then raise (NotDeterministic v) else SS.add v set);;

let checkDeterminismInName rulesInName grammar = reduce SS.empty rulesInName (fun rule set -> join set (lookahead rule grammar));;

let checkDeterminism grammar = List.for_all (fun (a, b) -> ignore (checkDeterminismInName b grammar); true) grammar.rulesByName;;

let collectAllRules rulesByName = mapConcat rulesByName (fun (a, b) -> b);;

let collectAllNonTerminals rulesByName = reduce SS.empty rulesByName (fun (a, b) set -> SS.add a set);;

let buildGrammar rulesByName =
	{
  	rulesByName;
  	rules = collectAllRules rulesByName;
  	nonTerminals = collectAllNonTerminals rulesByName
  };;

let grammar = buildGrammar [
  ( "I", [
    { name = "I"; rightside = [ "("; "I"; "*"; "F"; ")" ] };
    { name = "I"; rightside = [ "F" ] }
	] );
  ( "F", [
    { name = "F"; rightside = [ "x" ] }
  ] )
];;

assert (checkDeterminism grammar);;

print_string "Ok!";;

