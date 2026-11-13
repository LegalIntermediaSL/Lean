import Lake
open Lake DSL

package «lean-tt» where
  version := v!"0.1.0"
  description := "Repositorio de aprendizaje de Lean 4, Cálculo Lambda y Teoría de Tipos Dependientes"

@[default_target]
lean_lib «LeanTT» where
  roots := #[`LeanTT]
