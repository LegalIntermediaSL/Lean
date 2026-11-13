/-!
# Módulo 36: Conexiones de Galois (`α ⊣ γ`), Órdenes Parciales e Interpretación Abstracta
## Ámbito: Análisis Estático de Programas, Teoría del Orden y Adjunciones

En el análisis estático de programas (Cousot & Cousot, 1977) y en el álgebra moderna, una
**Conexión de Galois** entre un dominio concreto `(C, ≤_C)` y un dominio abstracto `(A, ≤_A)`
consta de una función de abstracción `α : C → A` y una función de concretización `γ : A → C`
tales que para todo `c : C` y `a : A`:
$$\alpha(c) \le_A a \;\Longleftrightarrow\; c \le_C \gamma(a)$$

En este módulo:
1. Formalizamos conjuntos parcialmente ordenados (`Poset`) y Conexiones de Galois.
2. **Demostramos formalmente** que de este único axioma de adjunción se deducen:
   - La **inflacionariedad (extensividad)** de $\gamma \circ \alpha$: $c \le_C \gamma(\alpha(c))$ (corrección de la abstracción).
   - La **deflacionariedad** de $\alpha \circ \gamma$: $\alpha(\gamma(a)) \le_A a$.
   - La **monotonía** tanto de $\alpha$ como de $\gamma$.
   - La **idempotencia** de $\alpha \circ \gamma \circ \alpha = \alpha$.
-/

namespace LeanTT.M36

universe u v

class Poset (P : Type u) where
  le       : P → P → Prop
  le_refl  : ∀ x : P, le x x
  le_trans : ∀ {x y z : P}, le x y → le y z → le x z
  le_antisymm : ∀ {x y : P}, le x y → le y x → x = y

infix:50 " ⊑ " => Poset.le

/-- Una Conexión de Galois `α ⊣ γ` entre dos Posets `C` (concreto) y `A` (abstracto) -/
structure GaloisConnection (C : Type u) (A : Type v) [Poset C] [Poset A] where
  alpha : C → A
  gamma : A → C
  adj   : ∀ (c : C) (a : A), (alpha c ⊑ a) ↔ (c ⊑ gamma a)

namespace GaloisConnection

variable {C : Type u} {A : Type v} [Poset C] [Poset A] (gc : GaloisConnection C A)

/-- 1. Unidad (Extensividad): `c ⊑ γ(α(c))` para todo estado concreto `c : C`.
    Demostración: En `α(c) ⊑ a ↔ c ⊑ γ(a)`, basta elegir `a := α(c)` y usar `le_refl`! -/
theorem unit_le (c : C) : c ⊑ gc.gamma (gc.alpha c) :=
  (gc.adj c (gc.alpha c)).mp (Poset.le_refl (gc.alpha c))

/-- 2. Counidad (Deflacionariedad): `α(γ(a)) ⊑ a` para todo estado abstracto `a : A`.
    Demostración: En `α(c) ⊑ a ↔ c ⊑ γ(a)`, basta elegir `c := γ(a)` y usar `le_refl`! -/
theorem counit_le (a : A) : gc.alpha (gc.gamma a) ⊑ a :=
  (gc.adj (gc.gamma a) a).mpr (Poset.le_refl (gc.gamma a))

/-- 3. Monotonía de la función de abstracción `α`: si `c1 ⊑ c2`, entonces `α(c1) ⊑ α(c2)` -/
theorem alpha_mono {c1 c2 : C} (h : c1 ⊑ c2) : gc.alpha c1 ⊑ gc.alpha c2 := by
  rw [gc.adj]
  exact Poset.le_trans h (gc.unit_le c2)

/-- 4. Monotonía de la función de concretización `γ`: si `a1 ⊑ a2`, entonces `γ(a1) ⊑ γ(a2)` -/
theorem gamma_mono {a1 a2 : A} (h : a1 ⊑ a2) : gc.gamma a1 ⊑ gc.gamma a2 := by
  rw [← gc.adj]
  exact Poset.le_trans (gc.counit_le a1) h

/-- 5. Identidad Triangular / Idempotencia de la Abstracción: `α(γ(α(c))) = α(c)` -/
theorem alpha_gamma_alpha (c : C) : gc.alpha (gc.gamma (gc.alpha c)) = gc.alpha c := by
  apply Poset.le_antisymm
  · exact gc.counit_le (gc.alpha c)
  · exact gc.alpha_mono (gc.unit_le c)

end GaloisConnection
end LeanTT.M36
