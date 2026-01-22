const std = @import("std");
const Buffer = std.ArrayList;
const Map = std.StringHashMap;

pub fn Set(comptime T: type) type {
	return struct {
		const Self = @This();
		data: Buffer(T),

		pub fn init(mem: *const std.mem.Allocator) Self {
			return Self{
				.data = Buffer(T).init(mem.*)
			};
		}

		pub fn put(self: *Self, elem: T) void {
			for (self.data.items) |item| {
				if (T.eql(elem, item)){
					return;
				}
			}
			self.data.append(elem)
				catch unreachable;
		}

		pub fn contains(self: *Self, elem: T) bool {
			for (self.data.items) |item| {
				if (T.eql(item, elem)){
					return true;
				}
			}
			return false;
		}

		pub fn remove(self: *Self, elem: T) bool {
			for (self.data.items, 0..) |item, i| {
				if (T.eql(item, elem)){
					_ = self.data.swapRemove(i);
					return true;
				}
			}
			return false;
		}

		pub fn eql(a: Self, b: Self) bool {
			if (a.data.items.len != b.data.items.len){
				return false;
			}
			outer: for (a.data.items) |i| {
				for (b.data.items) |k| {
					if (T.eql(i, k)){
						continue :outer;
					}
				}
				return false;
			}
			return true;
		}
	};
}

var STATE_IDENTIFIER: u64 = 0; 

const State = struct {
	name: []u8,
	id: u64,

	pub fn init(name: []u8) State {
		STATE_IDENTIFIER += 1;
		return State{
			.id = STATE_IDENTIFIER,
			.name = name
		};
	}

	pub fn eql(a: State, b: State) bool {
		return a.id == b.id;
	}
};

const Environment = struct {
	state: Set(State),
	rules: Set(Rule),

	pub fn init(mem: *const std.mem.Allocator) Environment {
		return Environment{
			.state = Set(State).init(mem),
			.rules = Set(Rule).init(mem)
		};
	}
};

const Rule = struct {
	requires: Set(State),
	consumes: Set(State),
	introduces: Set(State),

	pub fn init(mem: *const std.mem.Allocator) Rule {
		return Rule{
			.requires = Set(State).init(mem),
			.consumes = Set(State).init(mem),
			.introduces = Set(State).init(mem)
		};
	}

	pub fn evaluate(self: *Rule, environment: *Environment) bool {
		for (self.requires.data.items) |elem| {
			if (!environment.state.contains(elem)){
				return false;
			}
		}
		for (self.consumes.data.items) |elem| {
			environment.state.remove(elem);
		}
		for (self.introduces.data.items) |elem| {
			environment.state.put(elem);
		}
		return true;
	}

	pub fn eql(a: Rule, b: Rule) bool {
		return (Set(State).eql(a.requires, b.requires))
			and (Set(State).eql(a.consume, b.consume))
			and (Set(State).eql(a.introduces, b.introduces));
	}
};

pub fn main() !void {
	const allocator = std.heap.page_allocator;
	var main_mem = std.heap.ArenaAllocator.init(allocator);
	defer main_mem.deinit();
	const mem = main_mem.allocator();
	var rand = std.crypto.random;
	_ = std.Random.DefaultPrng.init(rand.int(u64));
	_ = Rule.init(&mem);
}
