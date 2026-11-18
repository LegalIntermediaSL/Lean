import LeanTT.Exercises.E02_WorkoutInductiveFamiliesAndEquality

/-!
# Solucionario Comentado 02: Familias Inductivas Indexadas, Transporte y Vectores
Soluciones detalladas de `LeanTT/Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean`
comparando reconocimiento de patrones dependiente y pruebas por inducción sobre familias indexadas.
-/

namespace LeanTT.Solutions.S02

open LeanTT.Exercises.E02
open LeanTT.Exercises.E02.VecE

universe u

/-- Solución 3 (Explicación del Unificador Dependiente de Lean 4):
    Cuando tenemos `v : VecE α (n + 1)`, el constructor `.nil : VecE α 0` es descartado
    automáticamente por el kernel porque `0` y `n + 1` tienen constructores distintos (`noConfusion`).
    Por eso `cases v` genera una única rama `.cons x xs`! -/
theorem sol3_cons_head_tail_detallado {α : Type u} {n : Nat} (v : VecE α (n + 1)) :
    VecE.cons (ej1_head v) (ej2_tail v) = v := by
  rcases v with _ | ⟨x, xs⟩
  rfl

/-- Solución 4 en Modo Término Recursivo Puro (sin usar `by`): -/
theorem sol4_map_id_term {α : Type u} : {n : Nat} → (v : VecE α n) →
    ej4_map (fun x => x) v = v
  | 0,     .nil       => rfl
  | _ + 1, .cons x xs => congrArg (VecE.cons x) (sol4_map_id_term xs)

/-- Solución 5 en Modo Término Recursivo Puro usando `congrArg`: -/
theorem sol5_map_map_term {α β γ : Type u} (f : α → β) (g : β → γ) :
    {n : Nat} → (v : VecE α n) →
    ej4_map g (ej4_map f v) = ej4_map (fun x => g (f x)) v
  | 0,     .nil       => rfl
  | _ + 1, .cons x xs => congrArg (VecE.cons (g (f x))) (sol5_map_map_term f g xs)

end LeanTT.Solutions.S02
