const std = @import("std");
const Buffer = std.ArrayList;
const Map = std.StringHashMap;

pub fn Set(comptime T: type, comptime eql: fn(T, T) bool) type {
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
				if (eql(elem, item)){
					return;
				}
			}
			self.data.append(elem)
				catch unreachable;
		}

		pub fn contains(self: *Self, elem: T) bool {
			for (self.data.items) |item| {
				if (eql(item, elem)){
					return true;
				}
			}
			return false;
		}

		pub fn remove(self: *Self, elem: T) bool {
			for (self.data.items, 0..) |item, i| {
				if (eql(item, elem)){
					_ = self.data.swapRemove(i);
					return true;
				}
			}
			return false;
		}
	};
}

pub fn u64eql(a: u64, b: u64) bool{
	return a == b;
}

pub fn main() !void {
	const allocator = std.heap.page_allocator;
	var main_mem = std.heap.ArenaAllocator.init(allocator);
	defer main_mem.deinit();
	const mem = main_mem.allocator();
	var rand = std.crypto.random;
	_ = std.Random.DefaultPrng.init(rand.int(u64));
	var set = Set(u64, u64eql).init(&mem);
	set.put(5);
	set.put(5);
	std.debug.print("{}\n", .{set.contains(5)});
	_ = set.remove(5);
	std.debug.print("{}\n", .{set.contains(5)});
}
