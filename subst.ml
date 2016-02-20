open Term

exception Inconsistent

(* Substitution, but not limited to variables *)

class ['a] t =
	let rec subst1 x (Node(f,ss) as s) (Node(g,ts)) =
		let ts' = List.map (subst1 x s) ts in
		if g = x then Node(f,ss@ts') else Node(g,ts')
	in
	object (x:'x)
		val table = Hashtbl.create 16
		method get_table = table
		method mem (f:'a) = Hashtbl.mem table f
		method find f = Hashtbl.find table f
		method add f s =
			try if x#find f <> s then raise Inconsistent
			with Not_found -> Hashtbl.add table f s
		method replace f s =
			Hashtbl.iter (fun g t -> Hashtbl.replace table g (subst1 f s t)) table;
			if not (x#mem f) then Hashtbl.add table f s;
		method compose (y:'x) =
			let (z:'x) = x#copy in
			let z_table = z#get_table in
			let iterer f s = Hashtbl.replace z_table f (y#subst s) in
			Hashtbl.iter iterer z_table;
			let iterer g t =
				if not (Hashtbl.mem z_table g) then Hashtbl.add z_table g t
			in
			Hashtbl.iter iterer y#get_table;
			z
		method copy = {< table = Hashtbl.copy table >}
		method subst (Node(f,ss)) =
			let ss' = List.map x#subst ss in
			if f#is_var then
				try let Node(g,ts) = x#find f in Node(g,ts@ss')
				with Not_found -> Node(f,ss')
			else Node(f,ss')
		method output os =
			if Hashtbl.length table = 0 then begin
				output_string os "[ ]\n";
			end else begin
				let iterer f s =
					output_string os "    ";
					f#output os;
					output_string os " := ";
					output_term os s;
					output_string os "\n";
				in
				output_string os "[\n";
				Hashtbl.iter iterer table;
				output_string os "]\n";
				flush os;
			end;
	end;;

let singleton f s = let ret = new t in ret#replace f s; ret

let unify =
	let rec sub1 unifier (Node(f,ss) as s) (Node(g,ts) as t) =
		if f = g then
			sub2 unifier ss ts
		else if f#is_var then
			if VarSet.mem f#name (varset t) then None else Some(unifier#replace f t; unifier)
		else if g#is_var then
			if VarSet.mem g#name (varset s) then None else Some(unifier#replace g s; unifier)
		else None
	and sub2 unifier ss ts =
		match ss, ts with
		| [], [] -> Some(unifier)
		| (s::ss), (t::ts) ->
			(
				match sub1 unifier s t with
				| None -> None
				| Some(unifier) -> sub2 unifier (List.map unifier#subst ss) (List.map unifier#subst ts)
			)
		| _ -> None
	in
	fun s t -> sub1 (new t) s t

let matches =
	let rec sub1 matcher (Node(f,ss) as s) (Node(g,ts)) =
		if g#is_var then
			try matcher#add g s; Some(matcher)
			with Inconsistent -> None
		else if f = g then
			sub2 matcher ss ts
		else None
	and sub2 matcher ss ts =
		match ss, ts with
		| [], [] -> Some(matcher)
		| (s::ss), (t::ts) ->
			(
				match sub1 matcher s t with
				| None -> None
				| Some(matcher) -> sub2 matcher ss ts
			)
		| _ -> None
	in
	fun s t -> sub1 (new t) s t

let rec rename renamer (Node(f,ss)) =
	Node(renamer f, List.map (rename renamer) ss)

let vrename v =
	let renamer f = new sym_basic f#ty (f#name ^ "_{" ^ v ^ "}") in
	rename renamer

