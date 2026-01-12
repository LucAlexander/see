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
		id: u64
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
	After: struct {
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
	AGE: Atom,
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

const Context = union(enum){
	inactive,
	active: Buffer(Atom)
};

const MAX_CONTEXTS = 8;

const Universe = struct {
	mem: *const std.mem.Allocator,
	constraints: Buffer(*Expr),
	invokable: Buffer(*Expr),
	contexts: [MAX_CONTEXTS] Context,
	step: u64,

	pub fn init(mem: *const std.mem.Allocator) Universe {
		var universe = Universe{
			.mem = mem,
			.constraints = Buffer(*Expr).init(mem.*),
			.invokable = Buffer(*Expr).init(mem.*),
			.contexts = undefined
		};
		for (0..MAX_CONTEXTS) |i| {
			universe.contexts[i] = Context{
				.inactive = .{}
			};
		}
		return universe;
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
	capabilities: Set,
	local_constraints: Buffer(*Expr),
	implications: Buffer(*Node),

	pub fn init(mem: *const std.mem.Allocator) Node {
		return Node{
			.value = null,
			.capabilities = Set.init(mem.*),
			.local_constraints = Buffer(*Expr).init(mem.*),
			.implications = Buffer(*Node).init(mem.*)
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

	pub fn init(mem: *const std.mem.Allocator, n: u64, complexity: u64, rand: std.Random) Graph {
		var graph = Graph{
			.nodes = Buffer(Node).init(mem.*),
			.matrix = Buffer(bool).init(mem.*),
			.n = n,
			.initial = Buffer(u64).init(mem.*),
			.terminal = Buffer(u64).init(mem.*),
			.difficulty = 0
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
	
};

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
