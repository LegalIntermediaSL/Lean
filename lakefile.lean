import Lake
open Lake DSL

package «LeanTT» where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

@[default_target]
lean_lib «LeanTT» where
  -- Compila LeanTT.lean y los 40 módulos LeanTT/M01..M40 + Exercises + Solutions
