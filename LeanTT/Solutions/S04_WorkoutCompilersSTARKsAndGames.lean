import LeanTT.Exercises.E04_WorkoutCompilersSTARKsAndGames

/-!
# Solucionario Comentado 04: Compilación CPS, Lógica Temporal LTL, STARKs/FRI, Teoría de Juegos y `wp`
Soluciones detalladas y teoremas complementarios de `LeanTT/Exercises/E04_WorkoutCompilersSTARKsAndGames.lean`.
-/

namespace LeanTT.Solutions.S04

open LeanTT.M53
open LeanTT.M56

/-- Solución Adicional 1 (Monotonía del Operador `Always` en LTL — Axioma K Temporal):
    Si `□(φ → ψ)` y `□ φ` se cumplen en una traza `τ`, entonces `□ ψ` también se cumple en `τ`. -/
theorem sol1_ltl_always_modus_ponens {State : Type} (φ ψ : LTLProp State) (τ : Trace State)
    (hImp : always (fun σ => φ σ → ψ σ) τ)
    (hPhi : always φ τ) :
    always ψ τ :=
  fun k => hImp k (hPhi k)

/-- Solución Adicional 2 (Idempotencia de `Always` en LTL: `□(□ φ) ↔ □ φ`): -/
theorem sol2_ltl_always_idempotent {State : Type} (φ : LTLProp State) (τ : Trace State) :
    always (always φ) τ ↔ always φ τ := by
  constructor
  · intro h k
    have hk := h k 0
    rwa [dropTrace_zero] at hk
  · intro h k1 k2
    rw [dropTrace_dropTrace]
    exact h (k1 + k2)

/-- Solución Adicional 3 (En la Subasta de Vickrey, sobrepujar cuando el rival puja más que
    nuestra valoración `v1 < b2 ≤ b1'` produce una utilidad estrictamente negativa `< 0`,
    lo que se conoce como la "Maldición del Ganador por Sobrepuja"): -/
theorem sol3_vickrey_overbidding_loss (v1 b1' b2 : Int)
    (hLoss : v1 < b2) (hWin : b2 ≤ b1') :
    vickreyUtility v1 b1' b2 < 0 := by
  dsimp [vickreyUtility]
  split <;> omega

end LeanTT.Solutions.S04
