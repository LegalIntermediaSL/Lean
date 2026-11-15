/-!
# Solucionario Comentado 01: Cálculo Lambda, Tipos Dependientes y Lógica Constructiva
Soluciones detalladas de `LeanTT/Exercises/E01_WorkoutLambdaAndLogic.lean` mostrando
tanto la versión en **Modo Término (λ puro)** como la versión en **Modo Táctico (`by`)**.
-/

namespace LeanTT.Solutions.S01

variable {P Q R : Prop}
variable {α β γ : Type}

/-- Solución 1: El combinador `C` de Curry (`flip`) -/
def sol1_flip : (α → β → γ) → (β → α → γ) :=
  fun f b a => f a b

/-- Solución 2: Por η y β-conversión en el kernel de Lean, `flip (flip f) ≡ f` -/
theorem sol2_flip_involutive (f : α → β → γ) :
    sol1_flip (sol1_flip f) = f :=
  rfl

/-- Solución 3A (Modo Término Puro): -/
theorem sol3_term : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) :=
  Iff.intro
    (fun h => ⟨fun hp => h (Or.inl hp), fun hq => h (Or.inr hq)⟩)
    (fun ⟨hpr, hqr⟩ hpq => Or.elim hpq hpr hqr)

/-- Solución 3B (Modo Táctico Paso a Paso): -/
theorem sol3_tactic : ((P ∨ Q) → R) ↔ (P → R) ∧ (Q → R) := by
  constructor
  · intro h
    constructor
    · intro hp
      apply h
      left
      exact hp
    · intro hq
      apply h
      right
      exact hq
  · intro h hpq
    rcases h with ⟨hpr, hqr⟩
    rcases hpq with hp | hq
    · exact hpr hp
    · exact hqr hq

/-- Solución 4A (Modo Término Puro — Proyección de Σ-Type y Subtipo): -/
theorem sol4_term (p : (n : Nat) × { m : Nat // n < m }) :
    p.1 < p.2.val :=
  p.2.property

/-- Solución 4B (Modo Táctico con Desestructuración `rcases`): -/
theorem sol4_tactic (p : (n : Nat) × { m : Nat // n < m }) :
    p.1 < p.2.val := by
  rcases p with ⟨_n, ⟨_m, hnm⟩⟩
  exact hnm

/-- Solución 5A (Por Inducción Estructural Explícita + Aritmética): -/
theorem sol5_induction (n : Nat) : n + n = 2 * n := by
  induction n with
  | zero => rfl
  | succ _k _ih => omega

/-- Solución 5B (Decisión Automática de Aritmética Lineal de Presburger con `omega`): -/
theorem sol5_omega (n : Nat) : n + n = 2 * n := by
  omega

end LeanTT.Solutions.S01
