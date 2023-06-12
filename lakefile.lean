import Lake
open Lake DSL

package «fp_lean» {
  -- add package configuration options here
}

lean_lib «FpLean» {
  -- add library configuration options here
}

@[default_target]
lean_exe «fp_lean» {
  root := `Main
}
