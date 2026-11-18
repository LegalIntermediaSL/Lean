import LeanTT.M21_NumberTheoryAndCryptography
import LeanTT.M32_ComputablePolynomialsAndFields
import LeanTT.M42_FiatShamirAndSigmaProtocols
import LeanTT.M43_AuthorizationPolicyEngineCedar

/-!
# Taller de Ejercicios 03: Verificación de Sistemas, Polinomios Computables y Criptografía ZK
Soluciones comentadas disponibles en: `LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean`

En este tercer taller aplicamos Lean 4 a problemas reales de verificación formal:
1. Puertas aritméticas de circuitos de Conocimiento Cero (R1CS / PlonK).
2. Evaluación de polinomios computables.
3. Invariantes de seguridad en motores de autorización y protocolos $\Sigma$.
-/

namespace LeanTT.Exercises.E03

/-- EJERCICIO 1 (Puerta Booleana NOT en un Circuito Aritmético ZK):
    En un circuito R1CS/PlonK, si un cable `b : Int` es booleano (`b = 0 ∨ b = 1`),
    su negación lógica se codifica aritméticamente como `1 - b`.
    Demuestra que `1 - b` también satisface la restricción cuadrática booleana `BitConstraint`! -/
theorem ej1_not_gate_preserves_bit (b : Int) (hb : LeanTT.M21.BitConstraint b) :
    LeanTT.M21.BitConstraint (1 - b) := by
  rw [LeanTT.M21.bitConstraint_iff] at hb ⊢
  rcases hb with rfl | rfl
  · right; rfl
  · left; rfl

/-- EJERCICIO 2 (Puerta AND en un Circuito Aritmético ZK):
    Si dos cables `a, b : Int` son booleanos, demuestra que su producto `a * b` también
    satisface `BitConstraint (a * b)`. -/
theorem ej2_and_gate_preserves_bit (a b : Int)
    (ha : LeanTT.M21.BitConstraint a) (hb : LeanTT.M21.BitConstraint b) :
    LeanTT.M21.BitConstraint (a * b) := by
  rw [LeanTT.M21.bitConstraint_iff] at ha hb ⊢
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> decide

/-- EJERCICIO 3 (Polinomio Cero en `CompPoly`):
    Demuestra que sumar el polinomio vacío `[]` por la derecha a cualquier `p : CompPoly`
    no altera su evaluación de Horner en ningún punto `x : Int`. -/
theorem ej3_evalHorner_add_nil (p : LeanTT.M32.CompPoly) (x : Int) :
    LeanTT.M32.evalHorner (LeanTT.M32.addPoly p []) x = LeanTT.M32.evalHorner p x := by
  rw [LeanTT.M32.evalHorner_addPoly]
  simp

/-- EJERCICIO 4 (Seguridad de Protocolos Σ ante Desafío Cero):
    En el Protocolo $\Sigma$ del Módulo 42, demuestra que si el Verifier envía el desafío
    `c = 0`, cualquier transcripción válida `verifySigma g y tr` cumple que `g * tr.response = tr.commit`
    (no depende en absoluto de la clave pública `y`). -/
theorem ej4_sigma_zero_challenge (g y : Int) (tr : LeanTT.M42.Transcript)
    (hc : tr.challenge = 0)
    (hv : LeanTT.M42.verifySigma g y tr) :
    g * tr.response = tr.commit := by
  dsimp [LeanTT.M42.verifySigma] at hv
  rw [hc] at hv
  omega

end LeanTT.Exercises.E03
