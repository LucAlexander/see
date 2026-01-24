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
				.data = Buffer(T).init(mem.*)
			};
			for (self.data.items) |elem| {
				set.data.append(elem.clone(mem))
					catch unreachable;
			}
			return set;
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
	id: union(enum){
		param:u64,
		state:u64
	},
	sub: union(enum){
		param:u64,
		state:u64
	},

	pub fn init(sub: u64, id: u64) State {
		return State{
			.sub = .{
				.state=sub
			},
			.id = .{
				.state=id
			}
		};
	}

	pub fn parameterize_sub(self: *State, param: u64, target: u64) bool {
		if (self.sub == .state){
			if (self.sub.state == target){
				self.sub = .{
					.param = param
				};
				return true;
			}
		}
		return false;
	}

	pub fn parameterize_id(self: *State, param: u64, target: u64) bool {
		if (self.id == .state){
			if (self.id.state == target){
				self.id = .{
					.param = param
				};
				return true;
			}
		}
		return false;
	}

	pub fn clone(self: *State, _: *const std.mem.Allocator) State {
		return self.*;
	}

	pub fn eql(a: State, b: State) bool {
		std.debug.assert(a.id == .state and b.id == .state and a.sub == .state and b.sub == .state);
		return (a.id.state == b.id.state) and (a.sub.state == b.sub.state);
	}
	
	pub fn show(self: *State) void {
		switch (self.sub) {
			.state => {
				std.debug.print("({} ", .{self.sub.state});
			},
			.param => {
				std.debug.print("([{}] ", .{self.sub.param});
			}
		}
		switch(self.id) {
			.state => {
				std.debug.print("{}) ", .{self.id.state});
			},
			.param => {
				std.debug.print("[{}]) ", .{self.id.param});
			}
		}
	}
};

const Environment = Set(State);

const Rule = struct {
	requires: Set(State),
	consumes: Set(State),
	introduces: Set(State),
	degree: u64,

	pub fn init(mem: *const std.mem.Allocator) Rule {
		return Rule{
			.requires = Set(State).init(mem),
			.consumes = Set(State).init(mem),
			.introduces = Set(State).init(mem),
			.degree = 0
		};
	}

	pub fn clone(self: *Rule, mem: *const std.mem.Allocator) Rule {
		return Rule{
			.requires = self.requires.clone(mem),
			.consumes = self.consumes.clone(mem),
			.introduces = self.introduces.clone(mem)
		};
	}

	pub fn parametric_on_sub(self: *Rule, param: u64) void {
		var found = false;
		for (self.requires.data.items) |*state| {
			if (state.parameterize_sub(param, self.degree)){
				found = true;
			}
		}
		for (self.consumes.data.items) |*state| {
			if (state.parameterize_sub(param, self.degree)){
				found = true;
			}
		}
		for (self.introduces.data.items) |*state| {
			if (state.parameterize_sub(param, self.degree)){
				found = true;
			}
		}
		if (found){
			self.degree += 1;
		}
	}
	
	pub fn parametric_on_id(self: *Rule, param: u64) void {
		var found = false;
		for (self.requires.data.items) |*state| {
			if (state.parameterize_id(param, self.degree)){
				found = true;
			}
		}
		for (self.consumes.data.items) |*state| {
			if (state.parameterize_id(param, self.degree)){
				found = true;
			}
		}
		for (self.introduces.data.items) |*state| {
			if (state.parameterize_id(param, self.degree)){
				found = true;
			}
		}
		if (found){
			self.degree += 1;
		}
	}
	
	pub fn apply(self: *Rule, param: std.AutoHashMap(u64, u64)) bool {
		for (self.requires.data.items) |*elem| {
			if (elem.id == .param){
				if (param.get(elem.id)) |replace| {
					elem.id = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
			if (elem.sub == .param){
				if (param.get(elem.sub)) |replace| {
					elem.sub = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
		}
		for (self.consumes.data.items) |*elem| {
			if (elem.id == .param){
				if (param.get(elem.id)) |replace| {
					elem.id = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
			if (elem.sub == .param){
				if (param.get(elem.sub)) |replace| {
					elem.sub = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
		}
		for (self.introduces.data.items) |*elem| {
			if (elem.id == .param){
				if (param.get(elem.id)) |replace| {
					elem.id = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
			if (elem.sub == .param){
				if (param.get(elem.sub)) |replace| {
					elem.sub = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
		}
		return true;
	}

	pub fn eval(self: *Rule, mem: *const std.mem.Allocator, environment: *Environment, param: std.AutoHashMap(u64, u64)) bool {
		var applied = self.clone(mem);
		if (applied.apply(param) == false) {
			return false;
		}
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

	pub fn show(self: *Rule) void {
		std.debug.print("Rule of degree {}\nrequires: ", .{self.degree});
		for (self.requires.data.items) |*state| {
			state.show();
		}
		std.debug.print("\nconsumes: ", .{});
		for (self.consumes.data.items) |*state| {
			state.show();
		}
		std.debug.print("\nproduces: ", .{});
		for (self.introduces.data.items) |*state| {
			state.show();
		}
		std.debug.print("\n\n", .{});
	}
};

const System = struct {
	rules: Set(Rule),
	env: Environment,
	mem: *const std.mem.Allocator,
	rng: std.Random,

	pub fn init(mem: *const std.mem.Allocator, rng: std.Random) System {
		const sys = System{
			.rules = Set(Rule).init(mem),
			.env = Environment.init(mem),
			.mem = mem,
			.rng = rng
		};
		const capabilities = rng.intRangeAtMost(u64, 8, 12);
		const users = rng.intRangeAtMost(u64, 2, 4);
		const rules = rng.intRangeAtMost(u64, 8, 16);
		for (0..rules) |_| {
			var rule = Rule.init(mem);
			var n = rng.intRangeAtMost(u64, 0, 4);
			for (0..n) |_| {
				const cap = rng.intRangeAtMost(u64, 0, capabilities-1);
				const use = rng.intRangeAtMost(u64, 0, users-1);
				const state = State.init(cap, use);
				rule.requires.put(state);
			}
			n = rng.intRangeAtMost(u64, 0, 4);
			for (0..n) |_| {
				const cap = rng.intRangeAtMost(u64, 0, capabilities-1);
				const use = rng.intRangeAtMost(u64, 0, users-1);
				const state = State.init(cap, use);
				rule.consumes.put(state);
			}
			n = rng.intRangeAtMost(u64, 0, 4);
			for (0..n) |_| {
				const cap = rng.intRangeAtMost(u64, 0, capabilities-1);
				const use = rng.intRangeAtMost(u64, 0, users-1);
				const state = State.init(cap, use);
				rule.introduces.put(state);
			}
			const parameters = rng.intRangeAtMost(u64, 0, 2);
			for (0..parameters) |_| {
				if (rng.intRangeAtMost(u64, 0, 1) == 0){
					const param = rng.intRangeAtMost(u64, 0, capabilities-1);
					rule.parametric_on_sub(param);
				}
				else{
					const param = rng.intRangeAtMost(u64, 0, users-1);
					rule.parametric_on_id(param);
				}
			}
			rule.show();
		}
		return sys;
	}

	pub fn show(self: *System) void {
		for (self.rules.data.items) |*rule| {
			rule.show();
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
	var sys = System.init(&mem, prng.random());
	sys.show();

}
