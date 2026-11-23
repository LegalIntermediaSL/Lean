import LeanTT.Exercises.E05_WorkoutQTTPostQuantumAndHardware

/-!
# Solucionario Comentado 05: QTT, Criptografía Post-Cuántica LWE, Redes Neuronales ReLU, CRDTs y Hardware
Soluciones detalladas y teoremas adicionales de `LeanTT/Exercises/E05_WorkoutQTTPostQuantumAndHardware.lean`.
-/

namespace LeanTT.Solutions.S05

open LeanTT.M61.Mult
open LeanTT.M63
open LeanTT.M65.GCounter3
open LeanTT.M66

/-- Solución Adicional 1 (Composición de Escalados de Contexto en QTT):
    Escalar un contexto `Γ` primero por `ρ` y luego por `π` equivale a escalarlo de una vez por `mulM π ρ`. -/
theorem sol1_scaleCtx_comp (π ρ : LeanTT.M61.Mult) (Γ : List LeanTT.M61.Mult) :
    scaleCtx π (scaleCtx ρ Γ) = scaleCtx (mulM π ρ) Γ := by
  induction Γ with
  | nil          => rfl
  | cons m ms ih =>
    simp only [scaleCtx, mulM_assoc, ih]

/-- Solución Adicional 2 (Anulación de `ReLU` en el Semieje Negativo):
    Para toda pre-activación `x ≤ 0` (*dead neuron regime*), `relu x = 0`. -/
theorem sol2_relu_eq_zero_of_nonpos {x : Int} (h : x ≤ 0) :
    relu x = 0 := by
  dsimp [relu]
  split <;> omega

/-- Solución Adicional 3 (Elemento Neutro `zero` del Semirretículo CRDT `GCounter3`):
    Fusionar cualquier réplica `c` con el estado vacío `GCounter3.zero` devuelve `c`. -/
@[simp]
theorem sol3_gcounter_merge_zero (c : LeanTT.M65.GCounter3) :
    merge c LeanTT.M65.GCounter3.zero = c := by
  cases c
  dsimp [merge, LeanTT.M65.GCounter3.zero]
  congr 1 <;> omega

/-- Solución Adicional 4 (Involutividad del Circuito `SWAP` Sintetizado con 3 Puertas `CNOT`):
    Aplicar dos veces la secuencia `cnot12 ∘ cnot21 ∘ cnot12` devuelve el registro cuántico original `s`. -/
theorem sol4_three_cnots_involutive (s : Reg2) :
    cnot12 (cnot21 (cnot12 (cnot12 (cnot21 (cnot12 s))))) = s := by
  cases s with | mk q1 q2 =>
  cases q1 <;> cases q2 <;> rfl

end LeanTT.Solutions.S05
