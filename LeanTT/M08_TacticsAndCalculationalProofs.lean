/-!
# Módulo 08: Modo Término vs. Modo Táctico (`by`), Pruebas Calculacionales (`calc`) y `conv`
Guía teórica asociada: `docs/08_tacticas_vs_terminos.md`

En este módulo exploramos:
1. Comparación lado a lado: la misma demostración escrita como término λ y con tácticas.
2. Inducción matemática y pruebas calculacionales (`calc`) sobre sumatorias.
3. Uso del modo de conversión dirigida (`conv`) para reescribir subtérminos específicos.
4. Automatización con `simp`, `omega` y `decide`.
-/

namespace LeanTT.M08

/-! ## 1. Comparación Directa: Término Lambda vs. Bloque Táctico `by` -/

/-- Versión 1: Término Lambda puro -/
theorem modus_tollens_term {P Q : Prop} : (P → Q) → ¬Q → ¬P :=
  fun hpq hnq hp => hnq (hpq hp)

/-- Versión 2: Bloque táctico `by` (produce exactamente el mismo término en el kernel) -/
theorem modus_tollens_tactic {P Q : Prop} : (P → Q) → ¬Q → ¬P := by
  intro hpq hnq hp
  apply hnq
  exact hpq hp

-- Verificamos que ambos términos de prueba son definicionalmente idénticos:
example {P Q : Prop} : @modus_tollens_term P Q = @modus_tollens_tactic P Q := rfl

/-! ## 2. Inducción Matemática + Bloques `calc` (Fórmula de Gauss) -/

/-- Suma de los primeros `n` números naturales: `0 + 1 + 2 + ... + n` -/
@[simp]
def sumUpTo : Nat → Nat
  | 0     => 0
  | n + 1 => sumUpTo n + (n + 1)

/-- Teorema de Gauss: `2 * sumUpTo n = n * (n + 1)`
    Demostrado combinando `induction`, una cadena calculacional `calc` y `omega`. -/
theorem gauss_formula (n : Nat) : 2 * sumUpTo n = n * (n + 1) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc
      2 * sumUpTo (k + 1)
        = 2 * (sumUpTo k + (k + 1)) := by rfl
      _ = 2 * sumUpTo k + 2 * (k + 1) := by rw [Nat.mul_add]
      _ = k * (k + 1) + 2 * (k + 1)   := by rw [ih]
      _ = (k + 1) * (k + 2)           := by omega

/-! ## 3. Verificación Formal de Algoritmos sobre Listas (`reverse`) -/

/-- La longitud de una lista se preserva al invertirla -/
theorem length_reverse {α : Type} (xs : List α) : xs.reverse.length = xs.length := by
  simp

/-- Invertir dos veces una lista devuelve la lista original -/
theorem reverse_involutive {α : Type} (xs : List α) : xs.reverse.reverse = xs := by
  simp

/-! ## 4. Reescritura Quirúrgica con el Modo `conv` -/

/-- Queremos demostrar `(a + b) + (c + d) = (b + a) + (c + d)` reescribiendo
    ÚNICAMENTE el primer sumando `(a + b)` en el lado izquierdo (`lhs`). -/
theorem reescritura_selectiva (a b c d : Nat) :
    (a + b) + (c + d) = (b + a) + (c + d) := by
  conv =>
    lhs
    congr
    · rw [Nat.add_comm]
    · rfl

/-! ## 5. Pruebas por Reflexión Computacional (`decide`) y Presburger (`omega`) -/

/-- `decide` verifica proposiciones decidibles evaluándolas en el kernel -/
example : (List.range 10).sum = 45 ∧ (17 % 5 = 2) := by
  decide

/-- `omega` resuelve sistemas de desigualdades lineales sobre `Nat` e `Int` -/
example (x y z : Int) (h1 : 2 * x + 3 * y ≤ 10) (h2 : y ≥ 4) (h3 : z = x + 1) :
    x ≤ -1 ∧ z ≤ 0 := by
  omega

end LeanTT.M08
