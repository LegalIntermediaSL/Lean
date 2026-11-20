import LeanTT.M51_ContinuationPassingStyleCPS
import LeanTT.M53_LinearTemporalLogicModelChecking
import LeanTT.M55_STARKsAndFRILowDegreeFolding
import LeanTT.M56_GameTheoryNashEquilibriumAndVCG
import LeanTT.M59_SymbolicExecutionAndWP

/-!
# Taller de Ejercicios 04: Compilación CPS, Lógica Temporal LTL, STARKs/FRI, Teoría de Juegos y `wp`
Soluciones detalladas disponibles en: `LeanTT/Solutions/S04_WorkoutCompilersSTARKsAndGames.lean`

En este cuarto taller práctico resolvemos problemas de los módulos `M51`–`M60`:
1. Transformación en estilo de paso de continuaciones (CPS).
2. Monotonía de operadores modales en Lógica Temporal Lineal (LTL).
3. Cancelación de términos pares en el protocolo FRI de zk-STARKs.
4. Dominancia débil en subastas de Vickrey y cálculo de `wp` de Dijkstra.
-/

namespace LeanTT.Exercises.E04

/-- EJERCICIO 1 (Evaluación CPS de una Suma):
    Demuestra que evaluar `.add e1 e2` mediante `runCPS` devuelve la suma de `runCPS e1` y `runCPS e2`. -/
theorem ej1_runCPS_add (e1 e2 : LeanTT.M51.Expr) :
    LeanTT.M51.runCPS (.add e1 e2) = LeanTT.M51.runCPS e1 + LeanTT.M51.runCPS e2 := by
  simp [LeanTT.M51.runCPS]

/-- EJERCICIO 2 (Distributividad de `Always` sobre la Conjunción en LTL):
    Demuestra que para toda traza `τ : Trace State`, `□(φ ∧ ψ)` equivale a `(□ φ) ∧ (□ ψ)`. -/
theorem ej2_ltl_always_and_iff {State : Type} (φ ψ : LeanTT.M53.LTLProp State)
    (τ : LeanTT.M53.Trace State) :
    LeanTT.M53.always (fun σ => φ σ ∧ ψ σ) τ ↔
      (LeanTT.M53.always φ τ ∧ LeanTT.M53.always ψ τ) := by
  constructor
  · intro h
    exact ⟨fun k => (h k).1, fun k => (h k).2⟩
  · rintro ⟨h1, h2⟩ k
    exact ⟨h1 k, h2 k⟩

/-- EJERCICIO 3 (Diferencia Simétrica en el Plegado FRI de STARKs):
    En el Módulo 55 demostramos que `P(x) + P(-x) = 2 · P_even(x²)`.
    Demuestra ahora la identidad dual para la parte impar:
    `P(x) - P(-x) = 2 · (P_odd(x²) · x)`! -/
theorem ej3_fri_symmetric_diff (P : LeanTT.M55.PolyDeg3) (x : Int) :
    LeanTT.M55.evalDeg3 P x - LeanTT.M55.evalDeg3 P (-x) =
      2 * (LeanTT.M55.evalDeg1 (LeanTT.M55.oddPart P) (x * x) * x) := by
  dsimp [LeanTT.M55.evalDeg3, LeanTT.M55.evalDeg1, LeanTT.M55.oddPart]
  have h_sq : (-x) * (-x) = x * x := Int.neg_mul_neg x x
  rw [h_sq, Int.mul_neg, Int.mul_neg, Int.add_mul]
  omega

/-- EJERCICIO 4 (Verificación con `wp` de Dijkstra de Incremento Doble):
    Usando `hoareTriple_iff_imp_wp` del Módulo 59, demuestra que ejecutar dos veces `x := x + 1`
    desde cualquier estado con `s.x = n` termina con `s.x = n + 2`. -/
theorem ej4_double_inc_wp (n : Int) :
    LeanTT.M59.HoareTriple
      (fun s => s.x = n)
      (.seq (.assignX (.add .varX (.const 1)))
            (.assignX (.add .varX (.const 1))))
      (fun s => s.x = n + 2) := by
  rw [LeanTT.M59.hoareTriple_iff_imp_wp]
  intro s hs
  dsimp [LeanTT.M59.wp, LeanTT.M59.evalAExp]
  omega

end LeanTT.Exercises.E04
