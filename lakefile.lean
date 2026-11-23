import Lake
open Lake DSL

package «LeanTT» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «LeanTT» where
  -- Compila LeanTT.lean, los 70 módulos LeanTT/M01..M70 y los 5 talleres Exercises/Solutions

@[default_target]
lean_exe «leantt» where
  root := `Main
