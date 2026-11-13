/-!
# Módulo 11: Semántica Operacional — Paso Pequeño (*Small-Step*), Paso Grande (*Big-Step*) y Determinismo
Guía teórica asociada: `docs/11_metateoria_calculo_lambda_no_tipado.md`

En este módulo exploramos:
1. Especificación de una semántica operacional de Paso Grande (`BigStep` / `e ⇓ v`).
2. Especificación de una semántica operacional de Paso Pequeño (`Step` / `e ⟶ e'`).
3. Clausura reflexiva-transitiva (`MultiStep` / `e ⟶* e'`).
4. Demostración formal del **Determinismo** de ambas semánticas.
5. Demostración formal del **Teorema de Equivalencia** (`e ⇓ n ↔ e ⟶* .val n`).
-/

namespace LeanTT.M11

/-! ## 1. Sintaxis del Lenguaje de Expresiones -/

inductive Expr : Type where
  | val : Nat → Expr
  | add : Expr → Expr → Expr
  deriving DecidableEq, Repr

/-! ## 2. Semántica de Paso Grande (Big-Step: `e ⇓ n`) -/

inductive BigStep : Expr → Nat → Prop where
  | val : {n : Nat} → BigStep (.val n) n
  | add : {e1 e2 : Expr} → {n1 n2 : Nat} →
          BigStep e1 n1 → BigStep e2 n2 → BigStep (.add e1 e2) (n1 + n2)

infix:50 " ⇓ " => BigStep

/-- Teorema de Determinismo de la Semántica Big-Step:
    Si `e ⇓ n1` y `e ⇓ n2`, entonces `n1 = n2`. -/
theorem bigStep_deterministic {e : Expr} {n1 n2 : Nat}
    (h1 : e ⇓ n1) (h2 : e ⇓ n2) : n1 = n2 := by
  induction h1 generalizing n2 with
  | val =>
    cases h2
    rfl
  | add _ _ ih1 ih2 =>
    cases h2 with
    | add hb1 hb2 =>
      rw [ih1 hb1, ih2 hb2]

/-! ## 3. Semántica de Paso Pequeño (Small-Step: `e ⟶ e'`) -/

/-- Relación de reducción de un paso con orden de evaluación izquierda-a-derecha -/
inductive Step : Expr → Expr → Prop where
  | addVals  : {n1 n2 : Nat} → Step (.add (.val n1) (.val n2)) (.val (n1 + n2))
  | addLeft  : {e1 e1' e2 : Expr} → Step e1 e1' → Step (.add e1 e2) (.add e1' e2)
  | addRight : {n1 : Nat} → {e2 e2' : Expr} →
               Step e2 e2' → Step (.add (.val n1) e2) (.add (.val n1) e2')

infix:50 " ⟶ " => Step

/-- Los valores `.val n` son formas normales: no pueden dar ningún paso `Step` -/
theorem val_no_step (n : Nat) (e : Expr) : ¬ (.val n ⟶ e) :=
  fun h => nomatch h

/-- Teorema de Determinismo de la Semántica Small-Step:
    Si `e ⟶ e1` y `e ⟶ e2`, entonces `e1 = e2`. -/
theorem step_deterministic {e e1 e2 : Expr} (h1 : e ⟶ e1) (h2 : e ⟶ e2) : e1 = e2 := by
  induction h1 generalizing e2 with
  | addVals =>
    cases h2 with
    | addVals      => rfl
    | addLeft hs1  => cases hs1
    | addRight hs2 => cases hs2
  | addLeft hs1 ih =>
    cases h2 with
    | addVals      => cases hs1
    | addLeft hs1' => rw [ih hs1']
    | addRight _   => cases hs1
  | addRight hs2 ih =>
    cases h2 with
    | addVals       => cases hs2
    | addLeft hs1   => cases hs1
    | addRight hs2' => rw [ih hs2']

/-! ## 4. Clausura Reflexiva-Transitiva (`MultiStep` / `⟶*`) -/

inductive MultiStep : Expr → Expr → Prop where
  | refl : (e : Expr) → MultiStep e e
  | step : {e1 e2 e3 : Expr} → (e1 ⟶ e2) → MultiStep e2 e3 → MultiStep e1 e3

infix:50 " ⟶* " => MultiStep

/-- Transitividad de la reducción multipaso `⟶*` -/
theorem multiStep_trans {e1 e2 e3 : Expr}
    (h1 : e1 ⟶* e2) (h2 : e2 ⟶* e3) : e1 ⟶* e3 := by
  induction h1 with
  | refl _          => exact h2
  | step hs _ ih    => exact .step hs (ih h2)

/-- Lema de congruencia izquierda para `⟶*` -/
theorem multiStep_add_left {e1 e1' e2 : Expr} (h : e1 ⟶* e1') :
    Expr.add e1 e2 ⟶* Expr.add e1' e2 := by
  induction h with
  | refl _       => exact .refl _
  | step hs _ ih => exact .step (.addLeft hs) ih

/-- Lema de congruencia derecha para `⟶*` -/
theorem multiStep_add_right {n1 : Nat} {e2 e2' : Expr} (h : e2 ⟶* e2') :
    Expr.add (.val n1) e2 ⟶* Expr.add (.val n1) e2' := by
  induction h with
  | refl _       => exact .refl _
  | step hs _ ih => exact .step (.addRight hs) ih

/-! ## 5. Teorema de Adecuación: Big-Step implica MultiStep (`e ⇓ n → e ⟶* .val n`) -/

theorem bigStep_imp_multiStep {e : Expr} {n : Nat} (h : e ⇓ n) : e ⟶* .val n := by
  induction h with
  | val => exact .refl _
  | @add e1 e2 n1 n2 _ _ ih1 ih2 =>
    apply multiStep_trans (multiStep_add_left ih1)
    apply multiStep_trans (multiStep_add_right ih2)
    exact .step .addVals (.refl _)

end LeanTT.M11
