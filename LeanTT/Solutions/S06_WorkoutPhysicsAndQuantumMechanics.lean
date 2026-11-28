import LeanTT.Exercises.E06_WorkoutPhysicsAndQuantumMechanics
import LeanTT.M73_HamiltonianMechanicsAndPoissonBrackets
import LeanTT.M78_QuantumEntanglementAndBellStates
import LeanTT.M79_NoCloningTeleportationAndDeutschJozsa

/-!
# Solucionario Comentado 06: Física Matemática, Mecánica Clásica, Relatividad y Computación Cuántica
Soluciones detalladas y teoremas complementarios de `LeanTT/Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean`.
-/

namespace LeanTT.Solutions.S06

open LeanTT.M71
open LeanTT.M73
open LeanTT.M76
open LeanTT.M77
open LeanTT.M78
open LeanTT.M80

/-- Solución Adicional 1 (Relación Dimensional Acción / Tiempo = Energía, $E = \hbar \omega$): -/
theorem sol1_action_div_time_eq_energy :
    Dim.div Dim.Action Dim.Time = Dim.Energy := by
  decide

/-- Solución Adicional 2 (Antisimetría del Conmutador de Lie-Poisson en $\mathfrak{sp}(2)$):
    Para todo par de generadores hamiltonianos `X, Y`, `[X, Y] + [Y, X] = 0`. -/
theorem sol2_sp2_lieBracket_antisymm (X Y : Sp2Elem) :
    sp2Add (lieBracket X Y) (lieBracket Y X) = sp2Zero := by
  cases X with | mk h1 e1 f1 =>
  cases Y with | mk h2 e2 f2 =>
  dsimp [sp2Add, lieBracket, sp2Zero]
  rw [Int.mul_comm e2 f1]
  simp only [Sp2Elem.mk.injEq]
  exact ⟨by omega, by omega, by omega⟩

/-- Solución Adicional 3 (Realidad del Valor Esperado del Espín $\sigma_z$):
    Aplicando el teorema espectral hermítico del Módulo 76 a `pauliZ`, su valor esperado en
    cualquier estado cuántico `ψ` tiene parte imaginaria nula. -/
theorem sol3_pauliZ_expectation_real (ψ : Ket2) :
    (braket ψ (applyMat2 pauliZ ψ)).im = 0 :=
  hermitian_expectation_is_real (by decide) ψ

/-- Solución Adicional 4 (Estado Singlete de Espín $\lvert\Psi^-\rangle = \lvert 01\rangle - \lvert 10\rangle$):
    Su norma cuadrática es `2` y su invariante de concurrencia de Schmidt es `0·0 - 1·(-1) = +1 ≠ 0`! -/
theorem sol4_singlet_norm_and_concurrence :
    braket4 bellPsiMinus bellPsiMinus = ⟨2, 0⟩ ∧
    schmidtDet bellPsiMinus = ⟨1, 0⟩ := by
  decide

/-- Solución Adicional 5 (Orden 4 de la Conjugación por la Puerta de Fase `S` sobre el Grupo de Pauli):
    Aplicar 4 veces la conjugación de Clifford por `S` actúa como la identidad sobre todo `SignedPauli`
    (ya que $S^4 = Z^2 = I$!). -/
theorem sol5_gottesman_knill_S_order4 (sp : SignedPauli) :
    conjugatePauliSymbolic .S
      (conjugatePauliSymbolic .S
        (conjugatePauliSymbolic .S
          (conjugatePauliSymbolic .S sp))) = sp := by
  cases sp with | mk neg sym =>
  cases neg <;> cases sym <;> rfl

end LeanTT.Solutions.S06
