const std = @import("std");
const Buffer = std.ArrayList;
const Map = std.StringHashMap;

const Node = struct{
	graph: u64,
	index: u64,
	next: Buffer(*Node),
	prev: Buffer(*Node),
	ref: Buffer(*Node),
	use: Buffer(*Node),

	pub fn init(mem: *const std.mem.Allocator, index: u64, graph_index: u64) *Node {
		const node = mem.create(Node)
			catch unreachable;
		node.* = Node{
			.next = Buffer(*Node).init(mem.*),
			.prev = Buffer(*Node).init(mem.*),
			.ref = Buffer(*Node).init(mem.*),
			.use = Buffer(*Node).init(mem.*),
			.index = index,
			.graph = graph_index
		};
		return node;
	}

	pub fn link(self: *Node, next: *Node) void {
		self.next.append(next)
			catch unreachable;
		next.prev.append(self)
			catch unreachable;
	}

	pub fn show(self: *Node) void {
		std.debug.print("node {}:{}\n", .{self.graph, self.index});
		for (self.next.items) |next| {
			std.debug.print(" -> {}:{}\n", .{next.graph, next.index});
		}
		for (self.ref.items) |ref| {
			std.debug.print(" &> {}:{}\n", .{ref.graph, ref.index});
		}
		for (self.use.items) |use| {
			std.debug.print(" <& {}:{}\n", .{use.graph, use.index});
		}
		std.debug.print("\n", .{});
	}
};

const Graph = struct{
	mem: *const std.mem.Allocator,
	rng: std.Random,
	nodes: Buffer(*Node),
	terminal: Buffer(*Node),
	index: u64,

	pub fn init(mem: *const std.mem.Allocator, n: u64, m: u64, rng: std.Random, index: u64) Graph {
		var graph = Graph{
			.mem = mem,
			.rng = rng,
			.nodes = Buffer(*Node).init(mem.*),
			.terminal = Buffer(*Node).init(mem.*),
			.index = index
		};
		while (graph.nodes.items.len < n or graph.nodes.items.len > m){
			graph.nodes.clearRetainingCapacity();
			const initial = graph.new();
			const terminal = graph.new();
			graph.path(initial, terminal, 3, 4);
		}
		for (graph.nodes.items) |node| {
			if (node.next.items.len == 0){
				graph.terminal.append(node)
					catch unreachable;
			}
		}
		return graph;
	}

	pub fn new(self: *Graph) *Node {
		const node = Node.init(self.mem, self.nodes.items.len, self.index);
		self.nodes.append(node)
			catch unreachable;
		return node;
	}

	pub fn path(self: *Graph, initial: *Node, terminal: *Node, min: u64, max: u64) void {
		const n = self.rng.intRangeAtMost(u64, min, max);
		var temp = initial;
		for (0..n) |_| {
			const node = self.new();
			temp.link(node);
			temp = node;
		}
		temp.link(terminal);
		temp = initial;
		for (0..n) |i| {
			if (temp.next.items.len == 0){
				break;
			}
			const next = temp.next.items[0];
			while (self.rng.intRangeAtMost(u64, 0, 2) == 0){
				if (self.rng.intRangeAtMost(u64, 0, 2) == 0){
					const early = self.new();
					self.path(next, early, 1, 2);
					continue;
				}
				var skipper = temp;
				for (i..n) |_| {
					if (skipper.next.items.len == 0){
						break;
					}
					skipper = skipper.next.items[0];
					if (self.rng.intRangeAtMost(u64, 0, 2) == 0){
						break;
					}
				}
				if (min/2 <= 2){
					self.path(temp, skipper, 1, 2);
				}
				else{
					self.path(temp, skipper, min/2, max/2);
				}
			}
			temp = next;
		}
	}

	pub fn show(self: *const Graph) void {
		for (self.nodes.items) |node| {
			node.show();
		}
	}
};

const System = struct {
	paths: Buffer(Graph),
	difficulty: u64,
	mem: *const std.mem.Allocator,
	rng: std.Random,

	pub fn init(mem: *const std.mem.Allocator, diff: u64, rng: std.Random) System {
		var sys = System{
			.paths = Buffer(Graph).init(mem.*),
			.difficulty = diff,
			.mem = mem,
			.rng = rng
		};
		var graph_count:u64 = 4;
		var range_min:u64 = 4;
		var range_max:u64 = 8;
		switch (diff){
			0 => {
				graph_count = 2;
				range_min = 2;
				range_max = 4;
			},
			1 => {
				graph_count = 2;
				range_min = 4;
				range_max = 6;
			},
			else => {}
		}
		for (0..graph_count) |i| {
			const graph = Graph.init(mem, range_min, range_max, rng, i);
			sys.paths.append(graph)
				catch unreachable;
		}
		while (rng.intRangeAtMost(u64, 0, 2) != 2){
			const source = sys.paths.items[rng.intRangeAtMost(u64, 0, sys.paths.items.len-1)];
			const term = source.terminal.items[rng.intRangeAtMost(u64, 0, source.terminal.items.len-1)];
			const destination = sys.paths.items[rng.intRangeAtMost(u64, 0, sys.paths.items.len-1)];
			const node = destination.nodes.items[rng.intRangeAtMost(u64, 0, destination.nodes.items.len-1)];
			term.ref.append(node)
				catch unreachable;
			node.use.append(term)
				catch unreachable;
		}
		return sys;
	}

	pub fn show(self: *System) void {
		for (self.paths.items, 0..) |path, i| {
			std.debug.print("Path {}:\n", .{i});
			path.show();
		}
	}
};

pub fn main() !void {
	const allocator = std.heap.page_allocator;
	var main_mem = std.heap.ArenaAllocator.init(allocator);
	defer main_mem.deinit();
	const mem = main_mem.allocator();
	var rand = std.crypto.random;
	var prng = std.Random.DefaultPrng.init(rand.int(u64));
	var system = System.init(&mem, 2, prng.random());
	system.show();
}
