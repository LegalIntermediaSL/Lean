/-!
# Taller de Ejercicios 01: Cálculo Lambda, Tipos Dependientes y Lógica Constructiva
 Soluciones completas disponibles en: `LeanTT/Solutions/S01_WorkoutLambdaAndLogic.lean`

Cada ejercicio está planteado y resuelto paso a paso con pistas graduales.
Para practicar por tu cuenta en VS Code:
1. Reemplaza el cuerpo de la demostración después de `:=` por `by sorry` (o `_`).
2. Coloca el cursor sobre el hueco y observa la meta en el **Lean Infoview**.
3. Usa las pistas para reconstruir la demostración tú mismo.
-/

namespace LeanTT.Exercises.E01

variable {P Q R : Prop}
variable {α β γ : Type}

/-- EJERCICIO 1 (Cálculo Lambda — Combinador `flip`):
    Define la función que invierte el orden de los dos argumentos de una función currificada.
    - Pista: `fun f b a => ...` -/
def ejercicio1_flip : (α → β → γ) → (β → α → γ) :=
  fun f b a => f a b

/-- EJERCICIO 2 (Demostración por β-reducción):
    Demuestra que aplicar `ejercicio1_flip` dos veces devuelve la función original `f`.
    - Pista: Como ambas funciones se reducen al mismo término, basta `rfl`. -/
theorem ejercicio2_flip_involutive (f : α → β → γ) :
    ejercicio1_flip (ejercicio1_flip f) = f :=
  rfl

/-- EJERCICIO 3 (Lógica Constructiva — Currificación de la Disyunción):
    Demuestra que `((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R)`.
    - Pista en modo táctico: usa `constructor`, `intro` y `rcases`. -/
theorem ejercicio3_or_imp_iff : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
  constructor
  · intro h
    exact ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩
  · rintro ⟨hpr, hqr⟩ (hp | hq)
    · exact hpr hp
    · exact hqr hq

/-- EJERCICIO 4 (Tipos Dependientes — Proyección de un Σ-Type con Invariante):
    Dado un par dependiente `p : (n : Nat) × { m : Nat // n < m }`, demuestra que `p.1 < p.2.val`.
    - Pista: la prueba ya está guardada dentro de `p.2.property`! -/
theorem ejercicio4_sigma_subtype (p : (n : Nat) × { m : Nat // n < m }) :
    p.1 < p.2.val :=
  p.2.property

/-- EJERCICIO 5 (Inducción sobre Naturales):
    Demuestra que para todo `n : Nat`, la suma `n + n` es igual a `2 * n`.
    - Pista: usa `omega` o inducción sobre `n`. -/
theorem ejercicio5_doble_eq_dos_por (n : Nat) : n + n = 2 * n := by
  omega

end LeanTT.Exercises.E01
