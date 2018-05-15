(* Utils *)

module SS = Set.Make(String);; (* Set<String> *)
module M = Map.Make(String);; (* Map<String, T> *)

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
type grammar = { rulesByName: (rule list) M.t; rules: rule list; nonTerminals: SS.t };;

let isTerminal variable grammar = SS.mem variable grammar.nonTerminals = false;;

let getRules variable rulesByName = let (_, b) = List.find (fun (a, b) -> a = variable) rulesByName in b;;

let rec canBeEmpty variables grammar =
	List.for_all (fun var -> canBeEmptyVariable var grammar) variables

and canBeEmptyVariable variable grammar =
	if isTerminal variable grammar then false else
		let rules = M.find variable grammar.rulesByName in List.exists (fun rule -> canBeEmpty rule.rightside grammar) rules;;

let rec first2 variables set grammar =
	match variables with
	| [] -> []
	| variable::rest -> if isTerminal variable grammar then variable::[] else firstRest rest set grammar @ firstVariable variable set grammar

and firstRest variables set grammar=
	if canBeEmpty variables grammar then first2 variables set grammar else []

and firstVariable variable set grammar =
	if SS.mem variable set then raise (LeftRecursive variable) else mapConcat (M.find variable grammar.rulesByName) (fun rule -> first2 rule.rightside (SS.add variable set) grammar);;

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

let checkDeterminism grammar = M.for_all (fun a b -> (ignore (checkDeterminismInName b grammar); true)) grammar.rulesByName;;

let collectAllRules rulesByName = mapConcat rulesByName (fun (a, b) -> b);;

let collectAllNonTerminals rulesByName = reduce SS.empty rulesByName (fun rule set -> SS.add rule.name set);;

let collectRulesByName rules =
	reduce M.empty rules (fun rule map -> let list = if M.mem rule.name map then rule::(M.find rule.name map) else rule::[] in M.add rule.name list map );;

let buildGrammar rules =
	{
  	rulesByName = collectRulesByName rules;
  	rules;
  	nonTerminals = collectAllNonTerminals rules
  };;

let grammar = buildGrammar [
  { name = "TYPESTATE"; rightside = [ "typestate"; "name"; "{"; "TYPESTATE_BODY"; "}" ] };
	
  { name = "TYPESTATE_BODY"; rightside = [ "empty" ] };
	{ name = "TYPESTATE_BODY"; rightside = [ "STATE_DEF"; "TYPESTATE_BODY" ] };
	
	{ name = "STATE_DEF_NAME"; rightside = [ "name"; "="; "STATE_DEF" ] };
	
	{ name = "STATE_DEF"; rightside = [ "{"; "STATES"; "}" ] };
	{ name = "STATES"; rightside = [ "empty" ] };
	{ name = "STATES"; rightside = [ "METHOD"; "STATE_NEXT" ] };
	{ name = "STATE_NEXT"; rightside = [ "empty" ] };
	{ name = "STATE_NEXT"; rightside = [ ","; "METHOD"; "STATE_NEXT" ] };
	
	{ name = "METHOD"; rightside = [ "type"; "name"; "("; "ARGUMENTS"; ")"; ":"; "W" ] };
	
	{ name = "ARGUMENTS"; rightside = [ "empty" ] };
	{ name = "ARGUMENTS"; rightside = [ "type"; "ARGUMENTS_NEXT" ] };
	{ name = "ARGUMENTS_NEXT"; rightside = [ "empty" ] };
	{ name = "ARGUMENTS_NEXT"; rightside = [ ","; "type"; "ARGUMENTS_NEXT" ] };
	
	{ name = "W"; rightside = [ "end" ] };
	{ name = "W"; rightside = [ "STATE_DEF" ] };
	{ name = "W"; rightside = [ "<"; "OPTIONS"; ">" ] };
	{ name = "W"; rightside = [ "name" ] };
	
	{ name = "OPTIONS"; rightside = [ "LABEL"; "OPTIONS_NEXT" ] };
	{ name = "OPTIONS_NEXT"; rightside = [ "empty" ] };
	{ name = "OPTIONS_NEXT"; rightside = [ ","; "OPTIONS" ] };
	
	{ name = "LABEL"; rightside = [ "name"; ":"; "LABEL_TO" ] };
	{ name = "LABEL_TO"; rightside = [ "end" ] };
	{ name = "LABEL_TO"; rightside = [ "name" ] };
	{ name = "LABEL_TO"; rightside = [ "STATE_DEF" ] };
];;

assert (checkDeterminism grammar);;

let parseTable grammar =
	reduce M.empty grammar.rules (fun rule map -> let map2 = if M.mem rule.name map then M.find rule.name map else M.empty in
  	M.add rule.name (
  		let newMap2 = reduce map2 (lookahead rule grammar) (fun s map -> M.add s rule map) in
				if canBeEmptyVariable rule.name grammar then M.add "empty" rule newMap2 else newMap2
  	) map
	);;

let listToStr list = reduce "" list (fun el str -> el ^ (if str = "" then "" else " ") ^ str);;

print_string ("Start: " ^ (match grammar.rules with rule::rest -> rule.name | [] -> "") ^ "\n\n");;

M.iter (fun name map -> M.iter (fun s rule -> print_string ("On " ^ name ^ ", if it finds \"" ^ s ^ "\", apply \"" ^ listToStr rule.rightside ^ "\"\n")) map) (parseTable grammar);;

print_string "\nOk!";;

