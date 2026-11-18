import LeanTT.Exercises.E03_WorkoutVerificationAndCryptography

/-!
# Solucionario Comentado 03: Verificación de Sistemas, Polinomios Computables y Criptografía ZK
Soluciones detalladas de `LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean`.
-/

namespace LeanTT.Solutions.S03

open LeanTT.M21

/-- Solución Alternativa al Ejercicio 1 (Demostración Algebraica Directa de `(1 - b) * (1 - (1 - b)) = 0`
    usando que `1 - (1 - b) = b` y la conmutatividad del producto en `Int`): -/
theorem sol1_not_gate_algebraic (b : Int) (hb : BitConstraint b) :
    BitConstraint (1 - b) := by
  dsimp [BitConstraint] at hb ⊢
  have h_simp : 1 - (1 - b) = b := by omega
  rw [h_simp, Int.mul_comm]
  exact hb

/-- Solución Adicional (Puerta OR Aritmética en Circuitos ZK):
    La disyunción inclusiva booleana se codifica en R1CS como `a + b - a * b`.
    Demostramos que si `a` y `b` son bits válidos, `a + b - a * b` también es un bit válido! -/
theorem sol_or_gate_preserves_bit (a b : Int)
    (ha : BitConstraint a) (hb : BitConstraint b) :
    BitConstraint (a + b - a * b) := by
  rw [bitConstraint_iff] at ha hb ⊢
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- Solución Adicional (Puerta XOR Aritmética en Circuitos ZK):
    El XOR booleano se codifica en R1CS como `a + b - 2 * a * b`.
    Demostramos que preserva `BitConstraint` para toda entrada booleana! -/
theorem sol_xor_gate_preserves_bit (a b : Int)
    (ha : BitConstraint a) (hb : BitConstraint b) :
    BitConstraint (a + b - 2 * a * b) := by
  rw [bitConstraint_iff] at ha hb ⊢
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

end LeanTT.Solutions.S03
