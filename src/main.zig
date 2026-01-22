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

		pub fn clone(self: *Self, mem: *const std.mem.Allocator) Self {
			var set = Self{
				.data = Buffer(T).init(mem.*);
			};
			for (self.data.items) |elem| {
				set.data.append(elem.clone(mem))
					catch unreachable;
			}
			return set
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

const State = struct {
	id: u64,
	sub: u64,

	pub fn init(sub: u64, id: u64) State {
		return State{
			.sub = sub,
			.id = id
		};
	}

	pub fn clone(self: *State, _: *const std.mem.Allocator) State {
		return self.*;
	}

	pub fn eql(a: State, b: State) bool {
		return (a.id == b.id) and (a.sub = b.sub);
	}
};

const Environment = Set(State);

const STATE_PARAM = 0;

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

	pub fn clone(self: *Rule, mem: *const std.mem.Allocator) Rule {
		return Rule{
			.requires = self.requires.clone(mem),
			.consumes = self.consumes.clone(mem),
			.introduces = self.introduces.clone(mem)
		};
	}
	
	pub fn apply(self: *Self, param: u64) void {
		for (self.requires.data.items) |*elem| {
			if (elem.id == STATE_PARAM){
				elem.id = param;
			}
			if (elem.sub == STATE_PARAM){
				elem.sum = param;
			}
		}
		for (self.consumes.data.items) |*elem| {
			if (elem.id == STATE_PARAM){
				elem.id = param;
			}
			if (elem.sub == STATE_PARAM){
				elem.sum = param;
			}
		}
		for (self.introduces.data.items) |*elem| {
			if (elem.id == STATE_PARAM){
				elem.id = param;
			}
			if (elem.sub == STATE_PARAM){
				elem.sum = param;
			}
		}
	}

	pub fn eval(self: *Rule, mem: *const std.mem.Allocator, environment: *Environment, param: u64) bool {
		var applied = self.clone(mem);
		applied.apply(param);
		for (applied.requires.data.items) |elem| {
			if (!environment.contains(elem)){
				return false;
			}
		}
		for (applied.consumes.data.items) |elem| {
			environment.remove(elem);
		}
		for (applied.introduces.data.items) |elem| {
			environment.put(elem);
		}
		return true;
	}

	pub fn eql(a: Rule, b: Rule) bool {
		return (Set(State).eql(a.requires, b.requires))
			and (Set(State).eql(a.consume, b.consume))
			and (Set(State).eql(a.introduces, b.introduces));
	}
};

const System = struct {
	rules: Set(Rule),
	env: Environment,
	mem: *const std.mem.Allocator,
	rng: std.Random,

	pub fn init(mem: *const std.mem.Allocator, rng: std.Random) System {
		var sys = System{
			.rules = Set(Rule).init(mem),
			.env = Environment.init(mem),
			.mem = mem,
			.rng = rng
		};
		const permissions = 3;
		const users = 2;
		const capabilities = 4;

		return sys;
	}
};

pub fn main() !void {
	const allocator = std.heap.page_allocator;
	var main_mem = std.heap.ArenaAllocator.init(allocator);
	defer main_mem.deinit();
	const mem = main_mem.allocator();
	var rand = std.crypto.random;
	var prng = std.Random.DefaultPrng.init(rand.int(u64));
	_ = System.init(&mem, prng.random());

}
