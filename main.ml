open Params
open Term
open Trs
open Dp
open Util
open Xml
open Io

type result =
| YES
| MAYBE
| NO

(* static usable rules *)
let static_usable_rules (trs : 'a trs) (estimator : 'a Estimator.t) (dg : 'a dg) used_dpset =
	if dg#minimal then (
		let used = Hashtbl.create 128 in
		let rec sub (Node(_,ts) as t) =
			let iterer i =
				if not (Hashtbl.mem used i) then begin
					let rule = trs#find_rule i in
					Hashtbl.add used i ();
					sub rule#r;
				end;
			in
			List.iter iterer (estimator#find_matchable t);
			List.iter sub ts;
		in
		IntSet.iter (fun i -> let Node(_,ts) = (dg#find_dp i)#r in List.iter sub ts) used_dpset;
	
		trs#fold_rules
		(fun i _ (usables,unusables) ->
			if Hashtbl.mem used i then (i::usables,unusables) else (usables,i::unusables)
		) ([],[])
	) else (
		trs#fold_rules (fun i _ is -> i::is) [], []
	)


let uncurry =
	if params.uncurry then
		fun (trs : #sym trs) (dg : #sym dg) ->
			comment (puts "Uncurrying");
			let appsyms = App.auto_uncurry trs dg in
			if appsyms = [] then
				(comment (puts " ... failed." >> endl); false)
			else (
				comment (fun (pr : #printer) ->
					List.iter (fun (a : #sym) -> pr#output_char ' '; a#output pr) appsyms;
					pr#cr;
				);
				problem trs#output;
				true
			)
	else
		fun _ _ -> false


let relative_test (trs : 'a trs) =
	trs#exists_rule (fun i rule ->
		if rule#is_weak && rule#is_duplicating then (
			comment (puts "Weak rule e" >> put_int i >> puts " is duplicating" >> endl);
			true
		) else if not(trs#const_term rule#r) then (
			comment (puts "Weak rule e" >> put_int i >> puts " calls a strict rule" >> endl);
			true
		) else false
	);;

let theory_test (trs : 'a trs) =
	let ths = trs#get_ths in
	let ths = StrSet.remove "A" ths in
	let ths = StrSet.remove "C" ths in
	let ths = StrSet.remove "AC" ths in
	if not (StrSet.is_empty ths) then begin
		warning (fun _ -> prerr_endline ("Unacceptable theories: " ^ StrSet.fold (^) ths ""));
		raise Unknown;
	end;;

(* extra variable test *)
let extra_test (trs : 'a trs) =
	let iterer i rule =
		if rule#has_extra_variable then begin
			proof (puts "Extra variable in rule " >> put_int i >> puts "." >> endl);
			raise Nonterm;
		end;
	in
	trs#iter_rules iterer;;

(* remove trivial relative rules *)
let trivial_test (trs : 'a trs) =
	let iterer i rule =
		if rule#l = rule#r then begin
			if rule#is_strict then begin
				proof (puts "Trivially nonterminating rule " >> put_int i >> puts "." >> endl);
				raise Nonterm;
			end else if rule#is_weak then begin
				proof (puts "Removing trivial weak rule " >> put_int i >> puts "." >> endl);
				trs#remove_rule i;
			end;
		end;
	in
	trs#iter_rules iterer;;


(* rule removal processor *)
let dummy_estimator = new Estimator.t (new trs)
let dummy_dg = new dg (new trs) dummy_estimator

let rule_remove (trs : 'a trs) =
	if Array.length params.orders_removal > 0 then begin
		let proc_list =
			let folder p procs =
				new Wpo.processor p trs dummy_estimator dummy_dg :: procs
			in
			Array.fold_right folder params.orders_removal []
		in
		let remove_strict rules =
			List.exists (fun proc -> proc#direct rules) proc_list
		in
		let rec loop () =
			let rules = trs#fold_rules (fun i _ is -> i::is) [] in
			comment (puts "Number of strict rules: " >> put_int trs#get_size_strict >> endl);
			if trs#get_size_strict = 0 then raise Success
			else if remove_strict rules then begin
				loop ();
			end else begin
				comment (puts " failed." >> endl);
			end;
		in
		loop ();
	end;;

(* reduction pair processor *)
let dp_remove (trs : 'a trs) (estimator : 'a Estimator.t) (dg : 'a dg) =
	let sccs = ref dg#get_sccs in
	let remove_unusable () =
		let init = ref true in
		let used_dpset = List.fold_left IntSet.union IntSet.empty !sccs in
		let curr_len = IntSet.cardinal used_dpset in
		if !init || curr_len < dg#get_size then begin
			log (puts "Removing unrelated DPs: {");
			init := false;
			let dp_remover i _ =
				if not (IntSet.mem i used_dpset) then
				begin
					log (puts " #" >> put_int i);
					dg#remove_dp i;
				end;
			in
			dg#iter_dps dp_remover;
			log (puts " }" >> endl);
(*
			log (fun _ -> prerr_string "Removing unusable rules: {");
			let (_,unusables) = static_usable_rules trs dg used_dpset in
			let rule_remover i =
				log (fun _ -> prerr_string " "; prerr_int i;);
				trs#remove_rule i;
			in
			List.iter rule_remover unusables;
			log (fun _ -> prerr_endline " }");
*)
		end;
	in
	let scc_sorter =
		let scc_size scc =
			IntSet.fold (fun i r -> dg#get_dp_size i + r) scc 0
		in
		match params.sort_scc with
		| SORT_asc ->
			List.sort (fun scc1 scc2 -> compare (scc_size scc1) (scc_size scc2))
		| SORT_desc ->
			List.sort (fun scc1 scc2 -> compare (scc_size scc1) (scc_size scc2))
		| SORT_none ->
			fun sccs -> sccs
	in
	sccs := scc_sorter !sccs;
	let given_up = ref false in
	let proc_list =
		Array.fold_right
		(fun p procs ->
			p.usable <- p.usable && dg#minimal;
			new Wpo.processor p trs estimator dg :: procs
		)
		params.orders_dp []
	in
	let remove_strict sccref =
		let (usables,_) = static_usable_rules trs estimator dg !sccref in
		let remove_by_proc proc =
			proc#reduce dg (if proc#using_usable then usables
				else trs#fold_rules (fun i _ is -> i::is) []) sccref
		in
		List.exists remove_by_proc proc_list
	in

	cpf (Xml.enter "acDPTerminationProof");
	let rec loop () =
		comment (puts "Number of SCCs: " >> put_int (List.length !sccs) >> endl);
		remove_unusable ();
		match !sccs with
		| [] ->
			if dg#next then begin
				cpf (Xml.enclose "acDPTerminationProof" dg#output_dps_xml);
				problem (puts "Next Dependency Pairs:\n" >> dg#output_dps);
				sccs := dg#get_sccs;
				loop ();
			end else begin
				cpf (Xml.leave "acDPTerminationProof");
				raise (if !given_up then Unknown else Success);
			end
		| scc::rest ->
			problem
			(fun pr ->
				pr#output_string "  SCC {";
				Abbrev.put_int_set " #" scc pr;
				pr#output_string " }\n    ";
			);
			if IntSet.for_all (fun i -> (dg#find_dp i)#is_weak) scc then begin
				comment (puts "only weak rules.");
				sccs := rest;
				loop ();
			end else begin
				let sccref = ref scc in
				if remove_strict sccref then begin
					sccs := scc_sorter (dg#get_subsccs !sccref) @ rest;
					log dg#output_edges;
					loop ();
				end else begin
					comment (puts "failed." >> endl);
					Nonterm.find_loop params.max_loop trs estimator dg scc;
				end
			end
	in
	loop ();;

let dp_prove (trs : 'a trs) =
	let estimator = new Estimator.t trs in
	log estimator#output_sym_graph;

	cpf (Xml.enter "acDependencyPairs");
(*	cpf (Xml.enclose "markedSymbols" (fun os -> output_string os "true");
*)	let dg = new dg trs estimator in
	dg#init;
	cpf (
		Xml.enclose "equations" (
			Xml.enclose "rules" (fun os ->
				trs#iter_rules (fun _ rule -> if rule#is_weak then rule#output_xml os;)
			)
		) >>
		Xml.enclose "dpEquations" (
			Xml.enclose "rules" (fun os ->
				dg#iter_dps (fun _ dp -> if dp#is_weak then dp#output_xml os;)
			)
		) >>
		Xml.enclose "dps" (
			Xml.enclose "rules" (fun os ->
				dg#iter_dps (fun _ dp -> if dp#is_strict then dp#output_xml os;)
			)
		)
	);
	problem (puts "Dependency Pairs:\n" >> dg#output_dps);
	log dg#output_edges;

	try dp_remove trs estimator dg with it ->
	cpf (Xml.leave "acDependencyPairs");
	raise it



let prove_termination (trs : 'a trs) =
	problem (puts "Input TRS:" >> endl >> trs#output);
	cpf (
		Xml.enclose "input" (Xml.enclose "acRewriteSystem" trs#output_xml) >>
		Xml.enclose_inline "cpfVersion" (puts "2.2") >>
		Xml.enter "proof" >>
		Xml.enter "acTerminationProof"
	);

	theory_test trs;

	let ret =
		try
			extra_test trs;
			trivial_test trs;
			rule_remove trs;
			if uncurry trs dummy_dg then rule_remove trs;
			if params.mode = MODE_order then raise Unknown;
			if params.rdp_mode = RDP_naive && relative_test trs then raise Unknown;
			dp_prove trs;
			raise Unknown;
		with
		| Success -> YES
		| Unknown -> MAYBE
		| Nonterm -> NO
	in
	cpf (
		Xml.leave "acTerminationProof" >>
		Xml.leave "proof" >>
		Xml.enclose "origin" (
			Xml.enclose "proofOrigin" (
				Xml.enclose "tool" (
					Xml.enclose_inline "name" (puts "NaTT") >>
					Xml.enclose_inline "version" (puts version)
				)
			)
		)
	);
	ret
;;

class main =
	let err msg = prerr_endline ("Error: " ^ msg ^ "!"); exit 1 in
	let warn msg = warning(fun _ -> prerr_endline ("Warning: " ^ msg ^ ".")) in
object (x)
	val trs = new trs

	method no_ac = not(StrSet.mem "AC" trs#get_ths)

	method duplicating = trs#exists_rule (fun _ rule -> rule#is_duplicating)

	method run =
		if params.file = "" then
			trs#read_stdin
		else
			trs#read params.file;

		cpf (fun pr ->
			pr#output_string "<?xml version=\"1.0\"?>";
			pr#cr;
			pr#output_string "<?xml-stylesheet type=\"text/xsl\" href=\"cpfHTML.xsl\"?>";
			Xml.enter "certificationProblem xmlns:xsi=\"http://www.w3.org/2001/XMLSchema-instance\" xsi:noNamespaceSchemaLocation=\"cpf.xsd\"" pr;
		);

		begin match params.mode with
		| MODE_higher_xml ->
			trs#output_xml_ho cout;
		| MODE_through ->
			trs#output cout;
		| MODE_flat ->
			trs#iter_rules (fun i rule -> trs#modify_rule i (flat rule#l) (flat rule#r));
			trs#output cout;
		| MODE_uncurry ->
			ignore (App.auto_uncurry trs (new dg (new trs) (new Estimator.t (new trs))));
			trs#output cout;
		| MODE_simple ->
			if trs#exists_rule (fun _ rule -> emb_le rule#l rule#r) then
				err "Not simple";
		| MODE_dup	->
			if x#duplicating then err "Duplicating TRS";
			warn "Non-duplicating TRS";
			exit 0;
		| MODE_id	->
			trs#iter_rules (fun i rule -> if term_eq rule#l rule#r then trs#remove_rule i);
			trs#output_wst cout;
		| MODE_dist	->
(*				let tester _ rule =
				match rule#r with
				| Node(Th "AC",_,
					[Node(Th "AC",_,[Node(Var,_,_); Node(Var,_,_)]);
					 Node(Th "AC",_,[Node(Var,_,_); Node(Var,_,_)]);
					]) ->
					(match rule#l with
					 | Node(Th "AC",_,
					 	[Node(Var,_,_);
						 Node(Th "AC",_,[Node(Var,_,_);Node(Var,_,_)]);
						]) -> true
					 | Node(Th "AC",_,
						[Node(Th "AC",_,[Node(Var,_,_);Node(Var,_,_)]);
						 Node(Var,_,_);
						]) -> true
					 | _ -> false
					)
				| _ -> false
			in
			if trs#exists_rule tester then
				print_endline "Distribution like rule"
			else if x#duplicating then
				print_endline "Duplicating TRS"
			else
				print_endline "";
*)()
		| MODE_relative_test ->
			if relative_test trs then exit 1;
		| _ ->
			Array.iter
				(fun p ->
					if not p.remove_all && nonmonotone p then
						err "Rule removal processor must be monotone";
				) params.orders_removal;
			let ans = prove_termination trs in
(*				cpf (fun os ->
				output_string os
				(	match ans with
					| YES	-> "<yes>"
					| NO	-> "<no>"
					| MAYBE	-> "<maybe>"
				);
				output_char os '\n';
			);
*)				cpf (Xml.leave "certificationProblem" >> endl);
			if not params.cpf then
				print_endline
				(	match ans with
					| YES	-> "YES"
					| NO	-> "NO"
					| MAYBE	-> "MAYBE"
				);
		end;
end;;

begin
	try
		(new main)#run;
		exit 0;
	with
	| Unsound s ->
		prerr_newline ();
		prerr_string "Unsound: ";
		prerr_endline s;
	| Proc.Dead cmd ->
		prerr_newline ();
		prerr_string "Proccess '";
		prerr_string cmd;
		prerr_endline "' is dead!";
	| Smt.Internal s ->
		prerr_newline ();
		prerr_string "SMT error: ";
		prerr_endline s;
	| Smt.Response(s,e) ->
		prerr_newline ();
		prerr_string "Unexpected SMT solver response to '";
		prerr_string s;
		prerr_endline "':";
		Smt.prerr_exp e;
		prerr_newline ();
	| No_support(s) ->
		prerr_newline ();
		prerr_string "Not supported: ";
		prerr_endline s;
end;
print_endline "ERR";
exit 1;

