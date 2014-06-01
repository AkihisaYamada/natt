open Format;;
open Lexing;;
open Trs_ast;;

let verbose = ref false;;

let check_trs f c =
	let lb = from_channel c in
	try
		lb.lex_curr_p <-
		{ pos_fname = f ; pos_lnum = 1; pos_cnum = 0; pos_bol = 0};
		let ast = Trs_parser.spec Trs_lexer.token lb in
		if !verbose then printf "parse ok@.";
		let env = Trs_sem.spec ast in
		if !verbose then 
		begin
			printf "semantics ok, function symbols are:@.";
			List.iter
			(fun (id,arity) ->
				match arity with
				| Trs_sem.Var -> ()
				| Trs_sem.Function x -> printf "%s: %d@." id !x)
			env
		end;
		ast
(*
    if !cime_output then Cime.output f env ast;
    if !db_output then db_trs f ast
*)
	with 
	| Parsing.Parse_error ->
		let loc = Lexing.lexeme_start_p lb in
		eprintf "%a: syntax error.@." Trs_ast.print_loc loc;
		exit 1
	| Trs_lexer.Lexing_error msg ->
		let loc = Lexing.lexeme_start_p lb in
		eprintf "%a: lexer error, %s.@." Trs_ast.print_loc loc msg;
		exit 1
	| Trs_sem.Sem_error(loc,msg) ->
		eprintf "%a: %s.@." Trs_ast.print_loc loc msg;
		exit 1;;
