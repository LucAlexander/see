const std = @import("std");
const Buffer = std.ArrayList;
const Map = std.StringHashMap;

const Set = Buffer(Atom);

const Atom = union(enum){
	instance: struct{
		id: u64,
		meta: u64,
		created_at: u64,
		lineage: Buffer(Atom)
	},
	global: struct {
		id: ?u64
	}
};

const Expr = union(enum){
	AND: struct{
		left: *Expr,
		right: *Expr
	},
	OR: struct {
		left: *Expr,
		right: *Expr
	},
	XOR: struct {
		left: *Expr,
		right: *Expr
	},
	LESS: struct {
		left: Atom,
		right: Atom
	},
	GREATER: struct {
		left: Atom,
		right: Atom
	},
	EQUAL: struct {
		left: Atom,
		right: Atom
	},
	IN: struct {
		sub: Atom,
		set: Set 
	},
	MATCH_LINEAGE: struct {
		left: Atom,
		right: Atom
	},
	BEFORE: struct {
		left: Atom,
		right: Atom
	},
	AFTER: struct {
		left: Atom,
		right: Atom
	},
	STEP_DIFF: struct {
		left: Atom,
		right: Atom
	},
	ALL_DISTINCT: Set,
	ANY: struct {
		predicate: *Expr,
		collection: Set
	},
	ALL: struct {
		predicate: *Expr,
		collection: Set
	},
	OLDEST: Set,
	YOUNGEST: Set,
	CONNECTED: struct {
		left: Atom,
		right: Atom
	},
	DISJOINT: struct {
		left_a: Atom,
		right_a: Atom,
		left_b: Atom,
		right_b: Atom
	},
	MONOTONIC: Set,
	CONSUME: Atom,
	FORBIDDEN: Atom,
	MERGE: struct {
		left: Atom,
		right: Atom
	},
	NOT: *Expr,
	ATOM: Atom
};

const Context = struct {
	mem: *const std.mem.Allocator,
	constraints: Buffer(*Expr),
	invokable: Buffer(*Expr),
	active: Buffer(Atom),
	graph: Graph,
	step: u64,

	pub fn init(mem: *const std.mem.Allocator, graph: Graph) Context {
		const context = Context{
			.mem = mem,
			.constraints = Buffer(*Expr).init(mem.*),
			.invokable = Buffer(*Expr).init(mem.*),
			.active = Buffer(Atom).init(mem.*),
			.graph = graph,
			.step = 0
		};
		for (graph.initial.items) |initial| {
			std.debug.assert(graph.nodes.items[initial].value != null);
			context.invokable.append(graph.nodes.items[initial].value.?)
				catch unreachable;
			context.constraints.appendSlice(graph.nodes.items[initial].local_constraints.items)
				catch unreachable;
		}
		return context;
	}
};

// generate a universe of capabilities, designate a few as targets
// build arbitrary DAG or DG
// assign expressions and local constraints
//   sometimes introduce an extrauniversal parameter and apply it to a stretch of the expression graph
// add global constraints to on atoms
// the user can not brute force because of reactivity and try limitation, but we can brute force to find a proof that there is still a possible path

const Node = struct {
	value: ?*Expr,
	capability: ?Atom,
	local_constraints: Buffer(*Expr),

	pub fn init(mem: *const std.mem.Allocator) Node {
		return Node{
			.value = null,
			.capability = null,
			.local_constraints = Buffer(*Expr).init(mem.*)
		};
	}
};

const Graph = struct {
	nodes: Buffer(Node),
	matrix: Buffer(bool),
	n: u64,
	initial: Buffer(u64),
	terminal: Buffer(u64),
	difficulty: u64,
	mem: *const std.mem.Allocator,
	rng: std.Random,

	pub fn init(mem: *const std.mem.Allocator, n: u64, complexity: u64, rand: std.Random) Graph {
		var graph = Graph{
			.nodes = Buffer(Node).init(mem.*),
			.matrix = Buffer(bool).init(mem.*),
			.n = n,
			.initial = Buffer(u64).init(mem.*),
			.terminal = Buffer(u64).init(mem.*),
			.difficulty = 0,
			.mem = mem,
			.rng = rand
		};
		for (0..n) |_| {
			graph.nodes.append(Node.init(mem))
				catch unreachable;
		}
		for (0..n) |x| {
			for (0..n) |y| {
				if (y<=x){
					graph.matrix.append(false)
						catch unreachable;
					continue;
				}
				if (rand.intRangeAtMost(u64, 0, complexity) == 0){
					graph.matrix.append(true)
						catch unreachable;
				}
				else{
					graph.matrix.append(false)
						catch unreachable;
				}
			}
		}
		outer: for (0..n) |y| {
			for (0..n) |x| {
				const index = (y*n) + x;
				if (graph.matrix.items[index]){
					continue :outer;
				}
			}
			graph.terminal.append(y)
				catch unreachable;
		}
		outer: for (0..n) |x| {
			for (0..n) |y| {
				const index = (y*n) + x;
				if (graph.matrix.items[index]){
					continue :outer;
				}
			}
			graph.initial.append(x)
				catch unreachable;
		}
		graph.difficulty = n-(graph.initial.items.len + graph.terminal.items.len);
		return graph;
	}

	pub fn show_matrix(self: *Graph) void {
		var index: u64 = 0;
		for (0..self.n) |_| {
			for (0..self.n) |_| {
				if (self.matrix.items[index]){
					std.debug.print("[x] ", .{});
					index += 1;
					continue;
				}
				std.debug.print("[ ] ", .{});
				index += 1;
			}
			std.debug.print("\n", .{});
		}
		std.debug.print("\n", .{});
		std.debug.print("initial nodes: [", .{});
		for (self.initial.items) |i| {
			std.debug.print("{} ", .{i});
		}
		std.debug.print("]\nterminal nodes: [", .{});
		for (self.terminal.items) |i| {
			std.debug.print("{} ", .{i});
		}
		std.debug.print("]\n", .{});
		std.debug.print("difficulty: {}\n", .{self.difficulty});
	}

	//TODO parameter propagation
	pub fn propagate(self: *Graph, universe: Set) void {
		for (self.nodes.items, universe.items) |node, capability| {
			node.capabiity = capability;
		}
		var local_universe = Set.int(self.mem.*);
		var layer = Buffer(u64).init(self.mem.*);
		var layer_q = Buffer(u64).init(self.mem.*);
		layer_q.appendSlice(self.initial.items)
			catch unreachable;
		while (layer.items.len > 0){
			layer.clearRetainingCapacity();
			layer.appendSlice(layer_q.items)
				catch unreachable;
			layer_q.clearRetainingCapacity();
			for (layer.items) |index| {
				const node = self.nodes.items[index];
				std.debug.assert(node.capability != null);
				local_universe.append(node.capability)
					catch unreachable;
				for (0..self.nodes.items.len) |target| {
					const subindex = (index * self.nodes.items.len) + target;
					if (self.matrix.items[subindex]){
						layer_q.append(target)
							catch unreachable;
					}
				}
				node.value = generate_predicate(self.mem, self.rng, local_universe, 3);
				while (self.rng.intRangeAtMost(u64, 0, 2) == 0){
					node.local_constraints.append(generate_predicate(self.mem, self.rng, local_universe, 3))
						catch unreachable;
				}
			}
		}
		for (self.nodes.items) |node| {
			std.debug.assert(node.value != null);
		}
	}
};

pub fn choose(rng: std.Random, local_universe: Set) Atom {
	const n = rng.intRangeAtMost(u64, 0, local_universe.items.len-1);
	return local_universe.items[n];
}

pub fn expr_atom(mem: *const std.mem.Allocator, atom: Atom) *Expr {
	const loc = mem.create(Expr);
	loc.* = Expr{
		.ATOM = atom
	};
	return loc;
}

pub fn noarg_atom() Atom {
	return Atom{
		.global = .{
			.id = null
		}
	};
}

pub fn generate_predicate(mem: *const std.mem.Allocator, rng: std.Random, local_universe: Set, max_depth: u64) *Expr {
	if (max_depth == 0 or rng.intRangeAtMost(0, 2) == 0){
		const loc = mem.create(Expr);
		loc.* = choose(rng, local_universe);
		return loc;
	}
	const options = 8;
	const n = rng.intRangeAtMost(u64, 0, options-1);
	const loc = mem.create(Expr);
	switch (n){
		0 => {
			loc.* = Expr{
				.AND = .{
					.left = generate_predicate(mem, rng, local_universe, max_depth-1),
					.right = generate_predicate(mem, rng, local_universe, max_depth-1)
				}
			};
			return loc;
		},
		1 => {
			loc.* = Expr{
				.OR = .{
					.left = generate_predicate(mem, rng, local_universe, max_depth-1),
					.right = generate_predicate(mem, rng, local_universe, max_depth-1)
				}
			};
			return loc;
		},
		2 => {
			loc.* = Expr{
				.XOR = .{
					.left = generate_predicate(mem, rng, local_universe, max_depth-1),
					.right = generate_predicate(mem, rng, local_universe, max_depth-1)
				}
			};
			return loc;
		},
		3 => {
			loc.* = Expr{
				.LESS = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		4 => {
			loc.* = Expr{
				.GREATER = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		5 => {
			loc.* = Expr{
				.LESS = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		6 => {
			loc.* = Expr{
				.IN = .{
					.sub = choose(rng, local_universe),
					.set = Set.init(mem.*)
				}
			};
			const cardinality = rng.intRangeAtMost(u64, 1, 4);
			for (0..cardinality) |_| {
				loc.IN.set.append(choose(rng, local_universe))
					catch unreachable;
			}
			return loc;
		},
		7 => {
			loc.* = Expr{
				.MATCH_LINEAGE = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		8 => {
			loc.* = Expr{
				.BEFORE = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		9 => {
			loc.* = Expr{
				.AFTER = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		10 => {
			loc.* = Expr{
				.STEP_DIFF = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		11 => {
			loc.* = Expr{
				.ALL_DISTINCT = Set.init(mem.*)
			};
			const cardinality = rng.intRangeAtMost(u64, 1, 4);
			for (0..cardinality) |_| {
				loc.ALL_DISTINCT.append(choose(rng, local_universe))
					catch unreachable;
			}
			return loc;
		},
		12 => {
			loc.* = Expr{
				.ANY = .{
					.predicate = generate_composable_predicate(mem, rng),
					.collecction = Set.init(mem.*)
				}
			};
			const cardinality = rng.intRangeAtMost(u64, 1, 4);
			for (0..cardinality) |_| {
				loc.ANY.append(choose(rng, local_universe))
					catch unreachable;
			}
			return loc;
		},
		13 => {
			loc.* = Expr{
				.ALL = .{
					.predicate = generate_composable_predicate(mem, rng),
					.collecction = Set.init(mem.*)
				}
			};
			const cardinality = rng.intRangeAtMost(u64, 1, 4);
			for (0..cardinality) |_| {
				loc.ALL.append(choose(rng, local_universe))
					catch unreachable;
			}
			return loc;
		},
		14 => {
			loc.* = Expr{
				.OLDEST = Set.init(mem.*)
			};
			const cardinality = rng.intRangeAtMost(u64, 1, 4);
			for (0..cardinality) |_| {
				loc.OLDEST.append(choose(rng, local_universe))
					catch unreachable;
			}
			return loc;
		},
		15 => {
			loc.* = Expr{
				.YOUNGEST = Set.init(mem.*)
			};
			const cardinality = rng.intRangeAtMost(u64, 1, 4);
			for (0..cardinality) |_| {
				loc.YOUNGEST.append(choose(rng, local_universe))
					catch unreachable;
			}
			return loc;
		},
		16 => {
			loc.* = Expr{
				.CONNECTED = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		17 => {
			loc.* = Expr{
				.MERGE = .{
					.left = choose(rng, local_universe),
					.right = choose(rng, local_universe)
				}
			};
			return loc;
		},
		18 => {
			loc.* = Expr{
				.DISJOINT = .{
					.left_a = choose(rng, local_universe),
					.right_a = choose(rng, local_universe),
					.left_b = choose(rng, local_universe),
					.right_b = choose(rng, local_universe)
				}
			};
			return loc;
		},
		19 => {
			loc.* = Expr{
				.MONOTONIC = Set.init(mem.*)
			};
			const cardinality = rng.intRangeAtMost(u64, 1, 4);
			for (0..cardinality) |_| {
				loc.MONOTONIC.append(choose(rng, local_universe))
					catch unreachable;
			}
			return loc;
		},
		20 => {
			loc.* = Expr{
				.CONSUME = choose(rng, local_universe)
			};
			return loc;
		},
		21 => {
			loc.* = Expr{
				.FORBIDDEN = choose(rng, local_universe)
			};
			return loc;
		},
		22 => {
			loc.* = Expr{
				.NOT = generate_predicate(mem, rng, local_universe, max_depth-1)
			};
			return loc;
		},
		else => {
			unreachable;
		}
	}
	unreachable;
}

pub fn generate_composable_predicate(mem: *const std.mem.Allocator, rng: std.Random) *Expr {
	if (rng.intRangeAtMost(0, 2) == 0){
		const loc = mem.create(Expr);
		loc.* = noarg_atom();
		return loc;
	}
	const options = 8;
	const n = rng.intRangeAtMost(u64, 0, options-1);
	const loc = mem.create(Expr);
	switch (n){
		0 => {
			loc.* = Expr{
				.AND = .{
					.left = generate_composable_predicate(mem, rng),
					.right = generate_composable_predicate(mem, rng)
				}
			};
			return loc;
		},
		1 => {
			loc.* = Expr{
				.OR = .{
					.left = generate_composable_predicate(mem, rng),
					.right = generate_composable_predicate(mem, rng)
				}
			};
			return loc;
		},
		2 => {
			loc.* = Expr{
				.XOR = .{
					.left = generate_composable_predicate(mem, rng),
					.right = generate_composable_predicate(mem, rng)
				}
			};
			return loc;
		},
		3 => {
			loc.* = Expr{
				.LESS = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		4 => {
			loc.* = Expr{
				.GREATER = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		5 => {
			loc.* = Expr{
				.LESS = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		6 => {
			loc.* = Expr{
				.IN = .{
					.sub = noarg_atom(),
					.set = Set.init(mem.*)
				}
			};
			return loc;
		},
		7 => {
			loc.* = Expr{
				.MATCH_LINEAGE = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		8 => {
			loc.* = Expr{
				.BEFORE = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		9 => {
			loc.* = Expr{
				.AFTER = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		10 => {
			loc.* = Expr{
				.STEP_DIFF = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		11 => {
			loc.* = Expr{
				.ALL_DISTINCT = Set.init(mem.*)
			};
			return loc;
		},
		12 => {
			loc.* = Expr{
				.ANY = .{
					.predicate = generate_composable_predicate(mem, rng),
					.collecction = Set.init(mem.*)
				}
			};
			return loc;
		},
		13 => {
			loc.* = Expr{
				.ALL = .{
					.predicate = generate_composable_predicate(mem, rng),
					.collecction = Set.init(mem.*)
				}
			};
			return loc;
		},
		14 => {
			loc.* = Expr{
				.OLDEST = Set.init(mem.*)
			};
			return loc;
		},
		15 => {
			loc.* = Expr{
				.YOUNGEST = Set.init(mem.*)
			};
			return loc;
		},
		16 => {
			loc.* = Expr{
				.CONNECTED = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		17 => {
			loc.* = Expr{
				.MERGE = .{
					.left = noarg_atom(),
					.right = noarg_atom()
				}
			};
			return loc;
		},
		18 => {
			loc.* = Expr{
				.DISJOINT = .{
					.left_a = noarg_atom(),
					.right_a = noarg_atom(),
					.left_b = noarg_atom(),
					.right_b = noarg_atom()
				}
			};
			return loc;
		},
		19 => {
			loc.* = Expr{
				.MONOTONIC = Set.init(mem.*)
			};
			return loc;
		},
		20 => {
			loc.* = Expr{
				.CONSUME = noarg_atom()
			};
			return loc;
		},
		21 => {
			loc.* = Expr{
				.FORBIDDEN = noarg_atom()
			};
			return loc;
		},
		22 => {
			loc.* = Expr{
				.NOT = generate_composable_predicate(mem, rng)
			};
			return loc;
		},
		else => {
			unreachable;
		}
	}
	unreachable;
}

pub fn show_expr(expr: *Expr) void {
	switch (expr.*){
		.AND => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("& ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.OR => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("| ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.XOR => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("^ ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.LESS => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("< ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.GREATER => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("> ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.EQUAL => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("= ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.IN => {
			std.debug.print("( ", .{});
			show_atom(expr.IN.sub);
			std.debug.print("in ", .{});
			show_set(expr.IN.set);
			std.debug.print(") ", .{});
		},
		.MATCH_LINEAGE => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print(">-> ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.BEFORE => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print(">> ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.AFTER => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("<< ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.STEP_DIFF => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print(".- ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.ALL_DISTINCT => {
			show_set(expr.ALL_DISTINCT);
		},
		.ANY => {
			std.debug.print("(any ", .{});
			show_expr(expr.ANY.predicate);
			std.debug.print("of ", .{});
			show_set(expr.ANY.collection);
			std.debug.print(") ", .{});
		},
		.ALL => {
			std.debug.print("(all ", .{});
			show_expr(expr.ANY.predicate);
			std.debug.print("of ", .{});
			show_set(expr.ANY.collection);
			std.debug.print(") ", .{});
		},
		.OLDEST => {
			std.debug.print("old ", .{});
			show_set(expr.OLDEST);
		},
		.YOUNGEST => {
			std.debug.print("young ", .{});
			show_set(expr.OLDEST);
		},
		.CONNECTED => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print("-- ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.DISJOINT => {
			std.debug.print("( ", .{});
			show_atom(expr.DISJOINT.left_a);
			show_atom(expr.DISJOINT.right_a);
			std.debug.print(") >x< ( ", .{});
			show_atom(expr.DISJOINT.left_b);
			show_atom(expr.DISJOINT.right_b);
			std.debug.print(") ", .{});
		},
		.MONOTONIC => {
			std.debug.print("(mono ", .{});
			show_set(expr.MONOTONIC);
			std.debug.print(") ", .{});
		},
		.CONSUME => {
			std.debug.print("/ ", .{});
			show_atom(expr.COMSUME);
		},
		.FORBIDDEN => {
			std.debug.print("! ", .{});
			show_atom(expr.FORBIDDEN);
		},
		.MERGE => {
			std.debug.print("( ", .{});
			show_expr(expr.AND.left);
			std.debug.print(">-< ", .{});
			show_expr(expr.AND.right);
			std.debug.print(") ", .{});
		},
		.NOT => {
			std.debug.print("~", .{});
			show_expr(expr.NOT);
		},
		.ATOM => {
			show_atom(expr.ATOM);
		}
	}
}

pub fn show_atom(atom: Atom) void {
	switch (atom){
		.instance => {
			std.debug.print("[{} {} {} <- ", .{atom.instance.id, atom.instance.meta, atom.instance.created_at});
			for (atom.instance.lineage) |ancestor| {
				std.debug.print("{} <- ", .{});
				show_atom(ancestor);
			}
			std.debug.print("] ", .{});
		},
		.global => {
			std.debug.print("[{}] ", .{atom.global.id});
		}
	}
}

pub fn show_set(set: Set) void {
	std.debug.print("( ", .{});
	for (set.items) |atom| {
		show_atom(atom);
	}
	std.debug.print(") ", .{});
}

const Problem = struct {
	graph: Graph,
	universe: Set,

	pub fn init(mem: *const std.mem.Allocator, n: u64, rand: std.Random) Problem {
		const complexity = (n/4)-1;
		const graph = Graph.init(mem, n, complexity, rand);
		const universe = Set.init(mem.*);
		for (0..n) |i| {
			universe.append(Atom{
				.global = .{
					.id = i
				}
			}) catch unreachable;
		}
		graph.propagate(mem, universe);
		return Problem{
			.graph = graph,
			.universe = universe
		};
	}
};

pub fn attempt(mem: *const std.mem.Allocator, problem: Problem) void {
	_ = Context.init(mem, problem.graph);
	//TODO
}

pub fn main() !void {
	var rand = std.crypto.random;
	var prng = std.Random.DefaultPrng.init(rand.int(u64));
	const allocator = std.heap.page_allocator;
	var main_mem = std.heap.ArenaAllocator.init(allocator);
	defer main_mem.deinit();
	const mem = main_mem.allocator();
	var graph = Graph.init(&mem, 16, 2, prng.random());
	graph.show_matrix();
}
