return {
    project = {
        name = "luaR",
    },

    luu = {
        install = {
            tools = true,
        },
    },

	luau = {
		languagemode = "strict",
		lint = { ["*"] = true },
		linterrors = true,
		aliases = {
			std = "~/.lute/typedefs/1.0.0/std",
			lute = "~/.lute/typedefs/1.0.0/lute",
			lint = "~/.lute/typedefs/1.0.0/lint",
		},
	},
    
	lute = {
		lint = {
			ignores = { "**/*.d.luau", "**/*.snap.luau" },
		},
		format = {
			ignores = {
				"**/*.d.luau",
				"**/generated-types.luau",
				"**/*unformatted*.luau",
				"tests/**"
			},
		},
	},
}