open Term

exception Inconsistent

class t =
	let rec subst1 xname s t =
		match t with
		| Node(Var,yname,[]) -> if xname = yname then s else t
		| Node(gty,gname,ts) -> Node(gty,gname,List.map (subst1 xname s) ts)
	in
	object (x:'x)
		val table = Hashtbl.create 16
		method get_table = table
		method mem xname = Hashtbl.mem table xname
		method find xname = Hashtbl.find table xname
		method add xname s =
			try if x#find xname <> s then raise Inconsistent
			with Not_found -> Hashtbl.add table xname s
		method replace xname s =
			Hashtbl.iter (fun yname t -> Hashtbl.replace table yname (subst1 xname s t)) table;
			if not (x#mem xname) then
				Hashtbl.add table xname s;
		method compose (y:'x) =
			let (z:'x) = x#copy in
			let z_table = z#get_table in
			let iterer xname s = Hashtbl.replace z_table xname (y#subst s) in
			Hashtbl.iter iterer z_table;
			let iterer yname t =
				if not (Hashtbl.mem z_table yname) then Hashtbl.add z_table yname t
			in
			Hashtbl.iter iterer y#get_table;
			z
		method copy = {< table = Hashtbl.copy table >}
		method subst s =
			match s with
			| Node(Var,xname,[]) -> (try x#find xname with Not_found -> s)
			| Node(fty,fname,ss) -> Node(fty, fname, List.map x#subst ss)
		method output os =
			if Hashtbl.length table = 0 then begin
				output_string os "[ ]\n";
			end else begin
				let iterer xname s =
					output_string os "    ";
					output_string os xname;
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

let singleton xname s = let ret = new t in ret#replace xname s; ret

let unify =
	let rec sub1 unifier (Node(fty,fname,ss) as s) (Node(gty,gname,ts) as t) =
		if fname = gname then
			sub2 unifier ss ts
		else if fty = Var then
			if VarSet.mem fname (varset t) then None else Some(unifier#replace fname t; unifier)
		else if gty = Var then
			if VarSet.mem gname (varset s) then None else Some(unifier#replace gname s; unifier)
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
	let rec sub1 matcher (Node(fty,fname,ss) as s) (Node(gty,gname,ts)) =
		if gty = Var then
			try matcher#add gname s; Some(matcher)
			with Inconsistent -> None
		else if fname = gname then
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

let rec rename f (Node(fty,fname,ss)) =
	if fty = Var then
		Node(fty, f fname, ss)
	else
		Node(fty, fname, List.map (rename f) ss)

let vrename v =
	let f vname = vname^ "_{" ^ v ^ "}" in
	rename f

