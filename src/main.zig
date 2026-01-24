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
			for (self.data.items) |*elem| {
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

pub fn Pop(comptime T: type) type {
	return struct {
		const Self = @This();
		data: T,
		count: u64,

		pub fn init(d: T) Self {
			return Self{
				.data = d,
				.count = 1
			};
		}
	};
}

pub fn PopSet(comptime T: type) type {
	return struct {
		const Self = @This();
		data: Buffer(Pop(T)),

		pub fn init(mem: *const std.mem.Allocator) Self {
			return Self{
				.data = Buffer(Pop(T)).init(mem.*)
			};
		}

		pub fn put(self: *Self, elem: T) void {
			for (self.data.items) |*item| {
				if (T.eql(elem, item.data)){
					item.count += 1;
					return;
				}
			}
			self.data.append(Pop(T).init(elem))
				catch unreachable;
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
		if (a.id == .state and b.id == .state){
			if (a.sub == .state and b.sub == .state){
				return (a.id.state == b.id.state) and (a.sub.state == b.sub.state);
			}
			if (a.sub == .param and b.sub == .param){
				return (a.id.state == b.id.state) and (a.sub.param == b.sub.param);
			}
		}
		if (a.id == .param and b.id == .param){
			if (a.sub == .param and b.sub == .param){
				return (a.id.param == b.id.param) and (a.sub.param == b.sub.param);
			}
			if (a.sub == .state and b.sub == .state){
				return (a.id.param == b.id.param) and (a.sub.state == b.sub.state);
			}
		}
		return false;
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
			.introduces = self.introduces.clone(mem),
			.degree = 0
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

	pub fn degree_is_sub(self: *Rule, degree: u64) bool {
		for (self.requires.data.items) |*state| {
			if (state.sub == .param){
				if (state.sub.param == degree){
					return true;
				}
			}
		}
		for (self.consumes.data.items) |*state| {
			if (state.sub == .param){
				if (state.sub.param == degree){
					return true;
				}
			}
		}
		for (self.introduces.data.items) |*state| {
			if (state.sub == .param){
				if (state.sub.param == degree){
					return true;
				}
			}
		}
		return false;
	}
	
	pub fn apply(self: *Rule, param: std.AutoHashMap(u64, u64)) bool {
		for (self.requires.data.items) |*elem| {
			if (elem.id == .param){
				if (param.get(elem.id.param)) |replace| {
					elem.id = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
			if (elem.sub == .param){
				if (param.get(elem.sub.param)) |replace| {
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
				if (param.get(elem.id.param)) |replace| {
					elem.id = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
			if (elem.sub == .param){
				if (param.get(elem.sub.param)) |replace| {
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
				if (param.get(elem.id.param)) |replace| {
					elem.id = .{
						.state = replace
					};
				}
				else{
					return false;
				}
			}
			if (elem.sub == .param){
				if (param.get(elem.sub.param)) |replace| {
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
			_ = environment.remove(elem);
		}
		for (applied.introduces.data.items) |elem| {
			environment.put(elem);
		}
		return true;
	}

	pub fn eql(a: Rule, b: Rule) bool {
		return (Set(State).eql(a.requires, b.requires))
			and (Set(State).eql(a.consumes, b.consumes))
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
	capabilities: u64,
	users: u64,

	pub fn init(mem: *const std.mem.Allocator, rng: std.Random) System {
		var sys = System{
			.rules = Set(Rule).init(mem),
			.env = Environment.init(mem),
			.mem = mem,
			.rng = rng,
			.capabilities = 0,
			.users = 0
		};
		const capabilities = rng.intRangeAtMost(u64, 8, 12);
		const users = rng.intRangeAtMost(u64, 2, 4);
		sys.capabilities = capabilities;
		sys.users = users;
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
			sys.rules.put(rule);
		}
		const initials = rng.intRangeAtMost(u64, 0, 4);
		for (0..initials) |_| {
			const cap = rng.intRangeAtMost(u64, 0, capabilities-1);
			const use = rng.intRangeAtMost(u64, 0, users-1);
			const state = State.init(cap, use);
			sys.env.put(state);
		}
		return sys;
	}

	pub fn shannon_entropy(self: *System, n: u64) f32 {
		var env = self.env.clone(self.mem);
		var step: u64 = 0;
		var stop = n*2;
		var count = PopSet(State).init(self.mem);
		outer:while (step < n) {
			var rule = self.rules.data.items[self.rng.intRangeAtMost(u64, 0, self.rules.data.items.len-1)];
			var param = std.AutoHashMap(u64, u64).init(self.mem.*);
			for (0..rule.degree) |target| {
				if (rule.degree_is_sub(target)){
					var cap:u64 = 0;
					var inner_stop:u64 = n;
					while (true) {
						cap = self.rng.intRangeAtMost(u64, 0, self.capabilities-1);
						if (environment_contains_cap(env, cap)){
							break;
						}
						inner_stop -= 1;
						if (inner_stop == 0){
							continue :outer;
						}
					}
					param.put(cap, target)
						catch unreachable;
				}
				else {
					var use:u64 = 0;
					var inner_stop: u64 = n;
					while (true){
						use = self.rng.intRangeAtMost(u64, 0, self.users-1);
						if (environment_contains_user(env, use)){
							break;
						}
						inner_stop -= 1;
						if (inner_stop == 0){
							continue :outer;
						}
					}
					param.put(use, target)
						catch unreachable;
				}
			}
			if (rule.eval(self.mem, &env, param)) {
				step += 1;
				stop = n*2;
				for (env.data.items) |state| {
					count.put(state);
				}
			}
			if (stop == 0){
				break;
			}
			stop -= 1;
		}
		var sum:f32 = 0;
		for (count.data.items) |pop| {
			const s: f32 = @as(f32, @floatFromInt(pop.count)) / @as(f32, @floatFromInt(n));
			sum += s * std.math.log2(s);
		}
		return sum;
	}

	pub fn show(self: *System) void {
		for (self.rules.data.items) |*rule| {
			rule.show();
		}
	}
};

pub fn environment_contains_user(env: Environment, user: u64) bool {
	for (env.data.items) |state| {
		std.debug.assert(state.id == .state);
		if (state.id.state == user){
			return true;
		}
	}
	return false;
}

pub fn environment_contains_cap(env: Environment, cap: u64) bool {
	for (env.data.items) |state| {
		std.debug.assert(state.sub == .state);
		if (state.sub.state == cap){
			return true;
		}
	}
	return false;
}

pub fn problem(mem: *const std.mem.Allocator, rng: std.Random, sample_size: u64) System {
	var systems = Buffer(System).init(mem.*);
	var entropies = Buffer(f32).init(mem.*);
	const n = 32;
	const trials = 4;
	for (0..sample_size) |_| {
		var sys = System.init(mem, rng);
		systems.append(sys)
			catch unreachable;
		var sum:f32 = 0;
		for (0..trials) |_| {
			sum += sys.shannon_entropy(n);
		}
		sum /= trials;
		entropies.append(sum)
			catch unreachable;
	}
	for (0..systems.items.len) |i| {
		for (i..systems.items.len) |j| {
			if (entropies.items[i] < entropies.items[j]){
				const temp = entropies.items[i];
				entropies.items[i] = entropies.items[j];
				entropies.items[j] = temp;
				const systemp = systems.items[i];
				systems.items[i] = systems.items[j];
				systems.items[j] = systemp;
			}
		}
	}
	const target = (entropies.items[entropies.items.len-1]-entropies.items[0])/2;
	var closest:u64 = 0;
	var close_diff:f32 = @abs(entropies.items[0]-target);
	for (1..systems.items.len) |i| {
		const diff = @abs(entropies.items[i] - target);
		if (diff < close_diff){
			close_diff = diff;
			closest = i;
		}
	}
	return systems.items[closest];
}

const Proc = struct {
	degree: u64,
	body: Buffer(Line)
};

const Data = union(enum) {
	data: u64,
	param: u64
};

const Line = union(enum) {
	read: struct {
		variable: Data,
		capability: Data
	},
	write: struct {
		capability: Data,
		user: Data
	},
	remove: struct {
		capability: Data,
		user: Data
	},
	call: struct {
		machine: u64,
		service: u64
	},
	conditional: struct {
		user: Data,
		variable: Data,
		body: ?Buffer(Line)
	}
};

const PROBLEM_PRECISION = 100;
const WORLD_SIZE = 32;

const Machine = struct {
	services: Buffer(System),

	pub fn init(mem: *const std.mem.Allocator, rng: std.Random, service_count: u64, pool: Buffer(System)) Machine {
		var mach = Machine{
			.services = Buffer(System).init(mem.*)
		};
		for (0 .. service_count) |_| {
			if (rng.intRangeAtMost(u64, 0, 2) == 0){
				mach.services.append(problem(mem, rng, PROBLEM_PRECISION))
					catch unreachable;
			}
			else{
				const index = rng.intRangeAtMost(u64, 0, pool.items.len-1);
				const service = pool.items[index];
				mach.services.append(service)
					catch unreachable;
			}
		}
		return mach;
	}
};

const Universe = struct{
	machines: Buffer(Machine),

	pub fn init(mem: *const std.mem.Allocator, rng: std.Random, n: u64) Universe {
		var uni = Universe{
			.machines = Buffer(Machine).init(mem.*)
		};
		var pool = Buffer(System).init(mem.*);
		for (0..n*4) |_| {
			pool.append(problem(mem, rng, PROBLEM_PRECISION))
				catch unreachable;
		}
		for (0..n) |_| {
			const service_count = rng.intRangeAtMost(u64, 1, 4);
			uni.machines.append(Machine.init(mem, rng, service_count, pool))
				catch unreachable;
		}
		return uni;
	}
	
	pub fn show(self: *Universe) void {
		var summary:u64 = 0;
		for (self.machines.items) |mach| {
			summary += mach.services.items.len;
		}
		std.debug.print("{} machines, {} nonunique services running total\n", .{self.machines.items.len, summary});
	}
};

pub fn main() !void {
	const allocator = std.heap.page_allocator;
	var main_mem = std.heap.ArenaAllocator.init(allocator);
	defer main_mem.deinit();
	const mem = main_mem.allocator();
	var rand = std.crypto.random;
	var prng = std.Random.DefaultPrng.init(rand.int(u64));
	var universe = Universe.init(&mem, prng.random(), WORLD_SIZE);
	universe.show();
}
