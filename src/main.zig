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
			if (state.parameterize_sub(self.degree, param)){
				found = true;
			}
		}
		for (self.consumes.data.items) |*state| {
			if (state.parameterize_sub(self.degree, param)){
				found = true;
			}
		}
		for (self.introduces.data.items) |*state| {
			if (state.parameterize_sub(self.degree, param)){
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
			if (state.parameterize_id(self.degree, param)){
				found = true;
			}
		}
		for (self.consumes.data.items) |*state| {
			if (state.parameterize_id(self.degree, param)){
				found = true;
			}
		}
		for (self.introduces.data.items) |*state| {
			if (state.parameterize_id(self.degree, param)){
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

pub fn clone_AutoHashMap( comptime K: type, comptime V: type, allocator: *const std.mem.Allocator, src: *const std.AutoHashMap(K, V),
) std.AutoHashMap(K, V) {
    var dst = std.AutoHashMap(K, V).init(allocator.*);
    dst.ensureTotalCapacity(src.count())
		catch unreachable;
    var it = src.iterator();
    while (it.next()) |entry| {
        dst.put(entry.key_ptr.*, entry.value_ptr.*)
			catch unreachable;
    }
    return dst;
}

const System = struct {
	rules: Set(Rule),
	env: Environment,
	mem: *const std.mem.Allocator,
	rng: std.Random,
	capabilities: u64,
	users: u64,
	target: State,

	pub fn init(mem: *const std.mem.Allocator, rng: std.Random, rules: u64) System {
		var sys = System{
			.rules = Set(Rule).init(mem),
			.env = Environment.init(mem),
			.mem = mem,
			.rng = rng,
			.capabilities = 0,
			.users = 0,
			.target = State.init(0, 0)
		};
		const capabilities = rng.intRangeAtMost(u64, 12, 24);
		const users = rng.intRangeAtMost(u64, 2, 4);
		sys.capabilities = capabilities;
		sys.users = users;
		const state_max = 2;
		for (0..rules) |_| {
			var rule = Rule.init(mem);
			var n = rng.intRangeAtMost(u64, 0, state_max);
			for (0..n) |_| {
				const cap = rng.intRangeAtMost(u64, 0, capabilities-1);
				const use = rng.intRangeAtMost(u64, 0, users-1);
				const state = State.init(cap, use);
				rule.requires.put(state);
			}
			n = rng.intRangeAtMost(u64, 0, state_max);
			for (0..n) |_| {
				const cap = rng.intRangeAtMost(u64, 0, capabilities-1);
				const use = rng.intRangeAtMost(u64, 0, users-1);
				const state = State.init(cap, use);
				rule.consumes.put(state);
			}
			n = rng.intRangeAtMost(u64, 0, state_max);
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
		const initials = rng.intRangeAtMost(u64, 2, 4);
		for (0..initials) |_| {
			const cap = rng.intRangeAtMost(u64, 0, capabilities-1);
			const use = rng.intRangeAtMost(u64, 0, users-1);
			const state = State.init(cap, use);
			sys.env.put(state);
		}
		return sys;
	}

	pub fn clone(self: *System, mem: *const std.mem.Allocator) System {
		return System{
			.rules = self.rules.clone(mem),
			.env = self.env.clone(mem),
			.mem = mem,
			.rng = self.rng,
			.capabilities = self.capabilities,
			.users = self.users,
			.target = self.target.clone(mem)
		};
	}

	pub fn determine_target(self: *System, n: u64, max_ways: u64) bool {
		var count = PopSet(State).init(self.mem);
		defer count.data.deinit();
		var iterations: u64 = 0;
		while (iterations < n){
			iterations += 1;
			var env = self.env.clone(self.mem);
			var stop = n*2;
			var step: u64 = 0;
			outer:while (step < n) {
				const rule_index = self.rng.intRangeAtMost(u64, 0, self.rules.data.items.len-1);
				var rule = self.rules.data.items[rule_index];
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
								step += 1;
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
								step += 1;
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
		}
		if (count.data.items.len == 0){
			return false;
		}
		var min: u64 = 0;
		var min_pop: u64 = count.data.items[0].count;
		for (count.data.items, 0..) |pop, i| {
			if (pop.count < min_pop) {
				min_pop = pop.count;
				min = i;
			}
		}
		if (min_pop > max_ways){
			return false;
		}
		const optimal = count.data.items[min].data;
		if (self.env.contains(optimal)){
			return false;
		}
		self.target = optimal;
		return true;
	}

	pub fn permutation_min_steps_to_target(self: *System, venv: *Environment, n: u64) ?u64 {
		var count: ?u64 = null;
		var iterations: u64 = 0;
		iterator: while (iterations < n){
			iterations += 1;
			var env = venv.clone(self.mem);
			var stop = n*2;
			var step: u64 = 0;
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
								step += 1;
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
								step += 1;
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
						if (State.eql(state, self.target)){
							if (count == null){
								count = step;
								iterations += 1;
								continue :iterator;
							}
							if (step < count.?){
								count = step;
								iterations += 1;
								continue :iterator;
							}
						}
					}
				}
				if (stop == 0){
					break;
				}
				stop -= 1;
			}
		}
		return count;
	}

	pub fn min_steps_to_target(self: *System, n: u64) u64 {
		var count:u64 = 1000;
		var iterations: u64 = 0;
		iterator: while (iterations < n){
			iterations += 1;
			var env = self.env.clone(self.mem);
			var stop = n*2;
			var step: u64 = 0;
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
								step += 1;
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
								step += 1;
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
						if (State.eql(state, self.target)){
							if (step < count){
								count = step;
								iterations += 1;
								continue :iterator;
							}
						}
					}
				}
				if (stop == 0){
					break;
				}
				stop -= 1;
			}
		}
		return count;
	}

	pub fn shannon_entropy(self: *System, n: u64) f32 {
		var env = self.env.clone(self.mem);
		var step: u64 = 0;
		var stop = n*2;
		var count = PopSet(State).init(self.mem);
		defer count.data.deinit();
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
							step += 1;
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
							step += 1;
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

	pub fn defensive_action_permutation(self: *System, rule: *Rule, env: *Environment, param: *std.AutoHashMap(u64, u64), permutations: []Buffer(u64), degree: u64, max_degree: u64, n: u64, permutation: Buffer(u64)) ?PermutationPair {
		if (degree == max_degree){
			var venv = env.clone(self.mem);
			if (rule.eval(self.mem, &venv, param.*)){
				var final_permutation = Buffer(u64).init(self.mem.*);
				final_permutation.appendSlice(permutation.items)
					catch unreachable;
				return PermutationPair{
					.arg = final_permutation,
					.val = self.permutation_min_steps_to_target(&venv, n),
				};
			}
			return null;
		}
		const layer = permutations[0];
		var max_case: ?PermutationPair = null;
		if (rule.degree_is_sub(degree)){
			for (0..layer.items.len) |i| {
				if (!environment_contains_cap(env.*, layer.items[i])){
					continue;
				}
				var param_copy = clone_AutoHashMap(u64, u64, self.mem, param);
				defer param_copy.deinit();
				param_copy.put(layer.items[i], degree)
					catch unreachable;
				var new_permutation = Buffer(u64).init(self.mem.*);
				new_permutation.appendSlice(permutation.items)
					catch unreachable;
				new_permutation.append(layer.items[i])
					catch unreachable;
				defer new_permutation.deinit();
				if (self.defensive_action_permutation(rule, env, &param_copy, permutations[1..permutations.len], degree+1, max_degree, n, new_permutation)) |val| {
					if (val.val) |v| {
						if (max_case == null){
							max_case = val;
						}
						else if (v > max_case.?.val.?) {
							max_case = val;
						}
					}
					else {
						return val;
					}
				}
			}
		}
		else{
			for (0..layer.items.len) |i| {
				if (!environment_contains_user(env.*, layer.items[i])){
					continue;
				}
				var param_copy = clone_AutoHashMap(u64, u64, self.mem, param);
				defer param_copy.deinit();
				param_copy.put(layer.items[i], degree)
					catch unreachable;
				var new_permutation = Buffer(u64).init(self.mem.*);
				new_permutation.appendSlice(permutation.items)
					catch unreachable;
				new_permutation.append(layer.items[i])
					catch unreachable;
				defer new_permutation.deinit();
				if (self.defensive_action_permutation(rule, env, &param_copy, permutations[1..permutations.len], degree+1, max_degree, n, new_permutation)) |val| {
					if (val.val) |v| {
						if (max_case == null){
							max_case = val;
						}
						else if (v > max_case.?.val.?) {
							max_case = val;
						}
					}
					else {
						return val;
					}
				}
			}
		}
		return max_case;
	}

	pub fn defensive_action(self: *System, n: u64) void {
		var min_index: u64 = 0;
		var min_param_set: ?PermutationPair = null;
		for (self.rules.data.items, 0..) |*rule, rule_index| {
			var param_permutations = Buffer(Buffer(u64)).init(self.mem.*);
			for (0..rule.degree) |_| {
				param_permutations.append(Buffer(u64).init(self.mem.*))
					catch unreachable;
			}
			for (0..rule.degree) |target| {
				if (rule.degree_is_sub(target)){
					for (0..self.capabilities) |cap| {
						param_permutations.items[target].append(cap)
							catch unreachable;
					}
				}
				else {
					for (0..self.users) |use| {
						param_permutations.items[target].append(use)
							catch unreachable;
					}
				}
			}
			var param = std.AutoHashMap(u64, u64).init(self.mem.*);
			var empty_permutation = Buffer(u64).init(self.mem.*);
			defer empty_permutation.deinit();
			if (self.defensive_action_permutation(rule, &self.env, &param, param_permutations.items, 0, rule.degree, n, empty_permutation)) |final_permutation| {
				std.debug.assert(rule.degree == final_permutation.arg.items.len);
				if (min_param_set == null){
					min_index = rule_index;
					min_param_set = final_permutation;
					if (min_param_set.?.val == null){
						break;
					}
					continue;
				}
				if (final_permutation.val) |v| {
					if (v > min_param_set.?.val.?){
						min_index = rule_index;
						min_param_set = final_permutation;
						continue;
					}
				}
			}
		}
		var rule = self.rules.data.items[min_index];
		if (min_param_set) |min| {
			var param = std.AutoHashMap(u64, u64).init(self.mem.*);
			for (0..rule.degree, min.arg.items) |target, arg| {
				param.put(arg, target)
					catch unreachable;
			}
			if (rule.eval(self.mem, &self.env, param)) {
				return;
			}
		}
	}

	pub fn offensive_action_permutation(self: *System, rule: *Rule, env: *Environment, param: *std.AutoHashMap(u64, u64), permutations: []Buffer(u64), degree: u64, max_degree: u64, n: u64, permutation: Buffer(u64)) ?PermutationPair {
		if (degree == max_degree){
			var venv = env.clone(self.mem);
			if (rule.eval(self.mem, &venv, param.*)){
				var final_permutation = Buffer(u64).init(self.mem.*);
				final_permutation.appendSlice(permutation.items)
					catch unreachable;
				return PermutationPair{
					.arg = final_permutation,
					.val = self.permutation_min_steps_to_target(&venv, n),
				};
			}
			return null;
		}
		const layer = permutations[0];
		var max_case: ?PermutationPair = null;
		if (rule.degree_is_sub(degree)){
			for (0..layer.items.len) |i| {
				if (!environment_contains_cap(env.*, layer.items[i])){
					continue;
				}
				var param_copy = clone_AutoHashMap(u64, u64, self.mem, param);
				defer param_copy.deinit();
				param_copy.put(layer.items[i], degree)
					catch unreachable;
				var new_permutation = Buffer(u64).init(self.mem.*);
				new_permutation.appendSlice(permutation.items)
					catch unreachable;
				new_permutation.append(layer.items[i])
					catch unreachable;
				defer new_permutation.deinit();
				if (self.offensive_action_permutation(rule, env, &param_copy, permutations[1..permutations.len], degree+1, max_degree, n, new_permutation)) |val| {
					if (val.val) |v| {
						if (max_case == null){
							max_case = val;
						}
						else if (v < max_case.?.val.?) {
							max_case = val;
						}
					}
					else {
						return val;
					}
				}
			}
		}
		else{
			for (0..layer.items.len) |i| {
				if (!environment_contains_user(env.*, layer.items[i])){
					continue;
				}
				var param_copy = clone_AutoHashMap(u64, u64, self.mem, param);
				defer param_copy.deinit();
				param_copy.put(layer.items[i], degree)
					catch unreachable;
				var new_permutation = Buffer(u64).init(self.mem.*);
				new_permutation.appendSlice(permutation.items)
					catch unreachable;
				new_permutation.append(layer.items[i])
					catch unreachable;
				defer new_permutation.deinit();
				if (self.offensive_action_permutation(rule, env, &param_copy, permutations[1..permutations.len], degree+1, max_degree, n, new_permutation)) |val| {
					if (val.val) |v| {
						if (max_case == null){
							max_case = val;
						}
						else if (v < max_case.?.val.?) {
							max_case = val;
						}
					}
					else {
						return val;
					}
				}
			}
		}
		return max_case;
	}

	pub fn offensive_action(self: *System, n: u64) void {
		var min_index: u64 = 0;
		var min_param_set: ?PermutationPair = null;
		for (self.rules.data.items, 0..) |*rule, rule_index| {
			var param_permutations = Buffer(Buffer(u64)).init(self.mem.*);
			for (0..rule.degree) |_| {
				param_permutations.append(Buffer(u64).init(self.mem.*))
					catch unreachable;
			}
			for (0..rule.degree) |target| {
				if (rule.degree_is_sub(target)){
					for (0..self.capabilities) |cap| {
						param_permutations.items[target].append(cap)
							catch unreachable;
					}
				}
				else {
					for (0..self.users) |use| {
						param_permutations.items[target].append(use)
							catch unreachable;
					}
				}
			}
			var param = std.AutoHashMap(u64, u64).init(self.mem.*);
			var empty_permutation = Buffer(u64).init(self.mem.*);
			defer empty_permutation.deinit();
			if (self.offensive_action_permutation(rule, &self.env, &param, param_permutations.items, 0, rule.degree, n, empty_permutation)) |final_permutation| {
				std.debug.assert(rule.degree == final_permutation.arg.items.len);
				if (min_param_set == null){
					min_index = rule_index;
					min_param_set = final_permutation;
					if (min_param_set.?.val == null){
						break;
					}
					continue;
				}
				if (final_permutation.val) |v| {
					if (v < min_param_set.?.val.?){
						min_index = rule_index;
						min_param_set = final_permutation;
						continue;
					}
				}
			}
		}
		var rule = self.rules.data.items[min_index];
		if (min_param_set) |min| {
			var param = std.AutoHashMap(u64, u64).init(self.mem.*);
			for (0..rule.degree, min.arg.items) |target, arg| {
				param.put(arg, target)
					catch unreachable;
			}
			if (rule.eval(self.mem, &self.env, param)) {
				return;
			}
		}
	}

	pub fn battle_sim(self: *System, n: u64) u64 {
		var sys = self.clone(self.mem);
		var steps: u64 = 0;
		var state: bool = false;
		while (steps < n) {
			if (state){
				sys.offensive_action(PROBLEM_PRECISION);
				sys.offensive_action(PROBLEM_PRECISION);
			}
			else{
				sys.defensive_action(PROBLEM_PRECISION);
			}
			state = !state;
			steps += 1;
			if (sys.env.contains(self.target)){
				return steps;
			}
		}
		return n;
	}

	pub fn show(self: *System) void {
		for (self.rules.data.items) |*rule| {
			rule.show();
		}
		std.debug.print("Starting environment: ", .{});
		for (self.env.data.items) |*state| {
			state.show();
		}
		std.debug.print("\nTarget capability: ", .{});
		self.target.show();
		std.debug.print("\n", .{});
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

pub fn attempt_problem(mem: *const std.mem.Allocator, rng: std.Random, sample_size: u64, trials: u64, steps: u64, rule_count: u64) ?System {
	var systems = Buffer(System).init(mem.*);
	defer systems.deinit();
	var entropies = Buffer(f32).init(mem.*);
	defer entropies.deinit();
	for (0..sample_size) |_| {
		var sys = System.init(mem, rng, rule_count);
		systems.append(sys)
			catch unreachable;
		var sum:f32 = 0;
		for (0..trials) |_| {
			sum += sys.shannon_entropy(steps);
		}
		sum /= @as(f32, @floatFromInt(trials));
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
	var best = systems.items[closest];
	if (best.determine_target(PROBLEM_PRECISION, MAX_WAYS)){
		const min_steps = best.battle_sim(PROBLEM_PRECISION);
		if (min_steps >= MIN_INTEREST){
			return best;
		}
	}
	return null;
}

pub fn problem(owner: *const std.mem.Allocator, rng: std.Random, sample_size: u64, trials: u64, steps: u64, rule_count: u64, max_retries: u64) ?System {
	var arena = std.heap.ArenaAllocator.init(std.heap.page_allocator);
	var mem = arena.allocator();
	for (0..max_retries) |_| {
		_ = arena.reset(.retain_capacity);
		var best = attempt_problem(&mem, rng, sample_size, trials, steps, rule_count);
		if (best) |_| {
			if (best.?.min_steps_to_target(PROBLEM_PRECISION) >= 3){
				return best.?.clone(owner);
			}
		}
	}
	return null;
}

const PermutationPair = struct {
	arg: Buffer(u64),
	val: ?u64
};

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

const PROBLEM_PRECISION = 16;
const WORLD_SIZE = 128;
const SYSTEM_SIZE = 32;
const MAX_WAYS = 3;
const MIN_INTEREST = 8;
const MAX_SERVICES = 5;

const Machine = struct {
	services: Buffer(System),

	pub fn init(mem: *const std.mem.Allocator, rng: std.Random, service_count: u64, pool: Buffer(System)) Machine {
		var mach = Machine{
			.services = Buffer(System).init(mem.*)
		};
		for (0 .. service_count) |_| {
			if (rng.intRangeAtMost(u64, 0, 2) == 0){
				if (problem(mem, rng, PROBLEM_PRECISION, PROBLEM_PRECISION, PROBLEM_PRECISION, SYSTEM_SIZE, 20)) |service| {
					mach.services.append(service)
						catch unreachable;
				}
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
		while (pool.items.len == 0) {
			for (0..n*4) |i| {
				if (problem(mem, rng, PROBLEM_PRECISION, PROBLEM_PRECISION, PROBLEM_PRECISION, SYSTEM_SIZE, 20)) |sys| {
					pool.append(sys)
						catch unreachable;
				}
				std.debug.print("\r{}%", .{(i*100)/(n*4)});
			}
			std.debug.print("\n", .{});
		}
		for (0..n) |i| {
			const service_count = rng.intRangeAtMost(u64, 1, MAX_SERVICES);
			uni.machines.append(Machine.init(mem, rng, service_count, pool))
				catch unreachable;
			std.debug.print("\r{}%", .{(i*100)/(n)});
		}
		std.debug.print("\n", .{});
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

//TODO 
// vectors of patching
// presentation layer
// interaction layer

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
