/-!
# Módulo 21: Teoría de Números, Aritmética Modular y Circuitos de Conocimiento Cero (ZK)
## Ámbito: Matemática Discreta, Criptografía Formal y Verificación de Circuitos (Estilo Clean / ArkLib)

En este módulo exploramos dos grandes áreas:
1. **Teoría de Números Constructiva:** La relación de divisibilidad `DvdNat m n` (`∃ k, n = m * k`),
   demostrando formalmente que es un preorden (reflexiva y transitiva) y que si `d` divide a `a`
   y a `b`, entonces divide a cualquier combinación lineal `x * a + y * b`.
2. **Verificación de Restricciones de Circuitos R1CS / AIR (Estilo `Clean` / `ArkLib`):**
   Cómo especificar en Lean 4 una puerta de circuito aritmético (p. ej. una restricción booleana
   `b * (1 - b) = 0` o un multiplexor `out = s * a + (1 - s) * b`) y demostrar formalmente su
   completitud (*Completeness*) y solidez (*Soundness*).
-/

namespace LeanTT.M21

/-! ## 1. Teoría de la Divisibilidad como Tipo Existencial -/

/-- `Divide m n` significa que existe un factor `k` tal que `n = m * k` -/
def Divide (m n : Nat) : Prop :=
  ∃ k : Nat, n = m * k

infix:50 " ∣ₙ " => Divide

/-- Reflexividad de la divisibilidad: todo número se divide a sí mismo (`n = n * 1`) -/
theorem divide_refl (n : Nat) : n ∣ₙ n :=
  ⟨1, by omega⟩

/-- Transitividad de la divisibilidad: si `a ∣ₙ b` y `b ∣ₙ c`, entonces `a ∣ₙ c` -/
theorem divide_trans {a b c : Nat} (hab : a ∣ₙ b) (hbc : b ∣ₙ c) : a ∣ₙ c := by
  rcases hab with ⟨k1, rfl⟩
  rcases hbc with ⟨k2, rfl⟩
  refine ⟨k1 * k2, ?_⟩
  rw [Nat.mul_assoc]

/-- Todo número divide a `0` (`0 = m * 0`) -/
theorem divide_zero (m : Nat) : m ∣ₙ 0 :=
  ⟨0, by omega⟩

/-- Si `d` divide a `a` y `d` divide a `b`, entonces `d` divide a `a + b` -/
theorem divide_add {d a b : Nat} (ha : d ∣ₙ a) (hb : d ∣ₙ b) : d ∣ₙ (a + b) := by
  rcases ha with ⟨ka, rfl⟩
  rcases hb with ⟨kb, rfl⟩
  refine ⟨ka + kb, ?_⟩
  rw [Nat.mul_add]

/-- Si `d` divide a `a`, entonces `d` divide a cualquier múltiplo `c * a` -/
theorem divide_mul_left {d a : Nat} (c : Nat) (ha : d ∣ₙ a) : d ∣ₙ (c * a) := by
  rcases ha with ⟨k, rfl⟩
  refine ⟨c * k, ?_⟩
  calc
    c * (d * k) = (c * d) * k := by rw [Nat.mul_assoc]
    _           = (d * c) * k := by rw [Nat.mul_comm c d]
    _           = d * (c * k) := by rw [Nat.mul_assoc]

/-- Teorema de Combinación Lineal: Si `d ∣ₙ a` y `d ∣ₙ b`, entonces `d ∣ₙ (x * a + y * b)` -/
theorem divide_linear_comb {d a b : Nat} (x y : Nat) (ha : d ∣ₙ a) (hb : d ∣ₙ b) :
    d ∣ₙ (x * a + y * b) :=
  divide_add (divide_mul_left x ha) (divide_mul_left y hb)

/-! ## 2. Verificación Formal de Puertas de Circuitos ZK (Estilo `Clean` / `ArkLib`) -/

/-- En los sistemas de pruebas de conocimiento cero (SNARKs / R1CS / Plonk), un cable `w : Int`
    se restringe a ser un bit (`0` o `1`) mediante la ecuación polinómica cuadrática:
    `w * (1 - w) = 0`. -/
def BitConstraint (w : Int) : Prop :=
  w * (1 - w) = 0

/-- Teorema de Completitud y Solidez (*Completeness & Soundness*) de la puerta de bit en `Int`:
    Un entero `w` satisface la restricción cuadrática `w * (1 - w) = 0`
    si y solo si `w = 0` o `w = 1`. -/
theorem bitConstraint_iff (w : Int) : BitConstraint w ↔ (w = 0 ∨ w = 1) := by
  dsimp [BitConstraint]
  constructor
  · intro h
    -- En un dominio entero, si `w * (1 - w) = 0`, entonces `w = 0` o `1 - w = 0`:
    cases Int.mul_eq_zero.mp h with
    | inl hw  => exact Or.inl hw
    | inr h1w =>
      right
      omega
  · intro h
    rcases h with rfl | rfl <;> rfl

/-- Puerta Multiplexora (Selector Condicional en un Circuito ZK):
    `MuxConstraint s a b out` impone que `s` sea un bit y que `out = b + s * (a - b)`.
    - Cuando `s = 0`, fuerza `out = b`.
    - Cuando `s = 1`, fuerza `out = a`. -/
def MuxConstraint (s a b out : Int) : Prop :=
  BitConstraint s ∧ out = b + s * (a - b)

/-- Demostración formal de la especificación funcional del circuito Multiplexor: -/
theorem mux_soundness (s a b out : Int) (h : MuxConstraint s a b out) :
    (s = 0 ∧ out = b) ∨ (s = 1 ∧ out = a) := by
  rcases h with ⟨hbit, hout⟩
  rcases (bitConstraint_iff s).mp hbit with rfl | rfl
  · left
    exact ⟨rfl, by omega⟩
  · right
    exact ⟨rfl, by omega⟩

end LeanTT.M21
