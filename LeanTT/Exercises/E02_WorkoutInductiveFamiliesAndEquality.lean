/-!
# Taller de Ejercicios 02: Familias Inductivas Indexadas, Transporte (`Eq.rec`) y Vectores
Soluciones comentadas disponibles en: `LeanTT/Solutions/S02_WorkoutInductiveFamiliesAndEquality.lean`

En este segundo taller practicamos la programación y demostración con **familias inductivas
indexadas** (`VecE α n`), el **principio de sustitución de Leibniz** y la **concatenación tipada**.
-/

namespace LeanTT.Exercises.E02

universe u v

/-- Familia inductiva de vectores de longitud exacta `n` para los ejercicios del Taller 02 -/
inductive VecE (α : Type u) : Nat → Type u where
  | nil  : VecE α 0
  | cons : {n : Nat} → α → VecE α n → VecE α (n + 1)
  deriving Repr, DecidableEq

namespace VecE

/-- EJERCICIO 1 (Cabeza segura en tiempo de compilación):
    Extrae el primer elemento de un vector no vacío `VecE α (n + 1)` sin usar `Option`. -/
def ej1_head {α : Type u} {n : Nat} : VecE α (n + 1) → α
  | .cons x _ => x

/-- EJERCICIO 2 (Cola segura en tiempo de compilación):
    Extrae la cola de longitud `n` de un vector `VecE α (n + 1)`. -/
def ej2_tail {α : Type u} {n : Nat} : VecE α (n + 1) → VecE α n
  | .cons _ xs => xs

/-- EJERCICIO 3 (Reconstrucción η de un vector no vacío):
    Demuestra por casos sobre `v : VecE α (n + 1)` que unir su cabeza y su cola reconstruye `v`. -/
theorem ej3_cons_head_tail {α : Type u} {n : Nat} (v : VecE α (n + 1)) :
    VecE.cons (ej1_head v) (ej2_tail v) = v := by
  cases v
  rfl

/-- EJERCICIO 4 (Mapeo preservando el índice de longitud `n`):
    Define `map` sobre `VecE α n` y demuestra que mapear la identidad devuelve el mismo vector. -/
@[simp]
def ej4_map {α : Type u} {β : Type v} {n : Nat} (f : α → β) : VecE α n → VecE β n
  | .nil       => .nil
  | .cons x xs => .cons (f x) (ej4_map f xs)

theorem ej4_map_id {α : Type u} {n : Nat} (v : VecE α n) :
    ej4_map (fun x => x) v = v := by
  induction v with
  | nil          => rfl
  | cons x xs ih => simp [ej4_map, ih]

/-- EJERCICIO 5 (Fusión de dos `map` sucesivos sin recorrer el vector dos veces):
    Demuestra que `ej4_map g (ej4_map f v) = ej4_map (fun x => g (f x)) v`. -/
theorem ej5_map_map {α β γ : Type u} {n : Nat} (f : α → β) (g : β → γ) (v : VecE α n) :
    ej4_map g (ej4_map f v) = ej4_map (fun x => g (f x)) v := by
  induction v with
  | nil          => rfl
  | cons x xs ih => simp [ej4_map, ih]

end VecE
end LeanTT.Exercises.E02
