--!strict
--- Task runner for the LuaR repository.
---
--- Every command here runs cargo. `lute luar test` is shorter than
--- `cargo run -q -p luarc -- test`, and that is all this file is for.

local process = require("@lute/process")

local USAGE = [[
luar, tasks for working on the compiler

usage:
  lute luar test [filter]     run the conformance suite
  lute luar check <file>...   read files and report what is wrong with them
  lute luar coverage          spec sections no test cites
  lute luar run <file>        run a program
  lute luar lir <file>        print what a program lowers to
  lute luar build             build the workspace
  lute luar unit              run the Rust tests
  lute luar fmt               format everything
  lute luar lint              clippy, warnings as errors
  lute luar ci                everything CI runs, in the order it runs it
]]

--- Runs cargo and passes its output straight through.
local function cargo(...: string): number
	local args = { "cargo", ... }
	return process.run(args, { stdio = "inherit" }).exitcode
end

--- Runs the compiler's command line with `rest` appended.
local function luarc(command: string, rest: { string }): number
	local args = { "cargo", "run", "-q", "-p", "luarc", "--", command }
	table.move(rest, 1, #rest, #args + 1, args)
	return process.run(args, { stdio = "inherit" }).exitcode
end

--- Formats the Luau in the repository, or reports on it when `check` is set.
--- Comes from `rokit.toml`.
local function stylua(check: boolean): number
	local args = { "stylua" }
	if check then
		table.insert(args, "--check")
	end
	table.insert(args, "luar.luau")
	return process.run(args, { stdio = "inherit" }).exitcode
end

--- Runs each step until one fails, and reports which one did.
local function sequence(steps: { { name: string, run: () -> number } }): number
	for _, step in steps do
		print(`\n=== {step.name}`)
		local code = step.run()
		if code ~= 0 then
			print(`\n{step.name} failed`)
			return code
		end
	end

	print("\neverything passed")
	return 0
end

local function format(): number
	local code = cargo("fmt", "--all")
	if code ~= 0 then
		return code
	end
	return stylua(false)
end

local function checkFormat(): number
	local code = cargo("fmt", "--all", "--check")
	if code ~= 0 then
		return code
	end
	return stylua(true)
end

local function lint(): number
	return cargo("clippy", "--workspace", "--all-targets", "--", "-D", "warnings")
end

local function unit(): number
	return cargo("test", "--workspace")
end

local function conformance(): number
	return luarc("test", {})
end

local commands: { [string]: (rest: { string }) -> number } = {
	test = function(rest)
		return luarc("test", rest)
	end,
	check = function(rest)
		return luarc("check", rest)
	end,
	coverage = function(rest)
		return luarc("coverage", rest)
	end,
	run = function(rest)
		return luarc("run", rest)
	end,
	lir = function(rest)
		return luarc("lir", rest)
	end,

	build = function()
		return cargo("build", "--workspace")
	end,
	unit = unit,
	fmt = format,
	lint = lint,

	ci = function()
		return sequence({
			{ name = "format", run = checkFormat },
			{ name = "lint", run = lint },
			{ name = "unit tests", run = unit },
			{ name = "conformance", run = conformance },
		})
	end,
}

-- `process.args[1]` is the script itself, so the command is the one after it.
local name = process.args[2]
if name == nil or name == "help" or name == "--help" or name == "-h" then
	print(USAGE)
	process.exit(if name == nil then 2 else 0)
end

local command = commands[name]
if command == nil then
	print(`luar: \`{name}\` is not a command\n`)
	print(USAGE)
	process.exit(2)
end

local rest = table.move(process.args, 3, #process.args, 1, {})
process.exit(command(rest))
