import LeanTT.M71_DimensionalAnalysisAndSIUnits
import LeanTT.M72_LagrangianMechanicsAndEulerLagrange
import LeanTT.M74_SpecialRelativityAndMinkowskiMetric
import LeanTT.M77_PauliCliffordAlgebraAndUnitarity
import LeanTT.M80_VerifiedQuantumCircuitCompilerAndStabilizers

/-!
# Taller de Ejercicios 06: Física Matemática, Mecánica Lagrangiana, Relatividad Especial y Computación Cuántica
Soluciones comentadas y teoremas adicionales en: `LeanTT/Solutions/S06_WorkoutPhysicsAndQuantumMechanics.lean`

En este sexto taller práctico consolidamos los módulos `M71`–`M80`:
1. Homogeneidad dimensional SI (`Potencia · Tiempo = Energía`).
2. Trayectorias inerciales como soluciones exactas de Euler-Lagrange.
3. Invariancia relativista de rayos luminosos sobre el cono de luz de Minkowski.
4. Superposición con fase negativa $\tilde{H}\lvert 1\rangle = \lvert -\rangle$.
5. Involutividad de la conjugación de Hadamard en el cuadro estabilizador de Gottesman-Knill.
-/

namespace LeanTT.Exercises.E06

/-- EJERCICIO 1 (Álgebra Dimensional SI):
    Demuestra que multiplicar la dimensión de `Power` (vatios) por `Time` (segundos) recupera
    exactamente la dimensión de `Energy` (julios). -/
theorem ej1_power_times_time_is_energy :
    LeanTT.M71.Dim.mul LeanTT.M71.Dim.Power LeanTT.M71.Dim.Time = LeanTT.M71.Dim.Energy := by
  decide

/-- EJERCICIO 2 (Movimiento Rectilíneo Uniforme y Principio de Hamilton):
    Demuestra que toda trayectoria con velocidad constante `(q0, q0 + v, q0 + 2 * v)` satisface
    exactamente la Ecuación de Euler-Lagrange Discreta para una partícula libre de masa `m`. -/
theorem ej2_uniform_motion_satisfies_euler_lagrange (m q0 v : Int) :
    LeanTT.M72.SatisfiesDEL (LeanTT.M72.freeParticle m) q0 (q0 + v) (q0 + 2 * v) := by
  dsimp [LeanTT.M72.SatisfiesDEL, LeanTT.M72.freeParticle]
  have h1 : (q0 + v) - q0 = v := by omega
  have h2 : (q0 + 2 * v) - (q0 + v) = v := by omega
  rw [h1, h2]
  omega

/-- EJERCICIO 3 (Propagación de un Fotón e Invariancia de Lorentz):
    Demuestra que el evento luminoso `⟨t, t, 0, 0⟩` pertenece al cono de luz (`IsLightlike`) y
    que sigue perteneciendo al cono de luz tras aplicar cualquier *boost* de Lorentz `B`. -/
theorem ej3_photon_worldline_lorentz_invariant (B : LeanTT.M74.ScaledBoostX) (t : Int) :
    LeanTT.M74.FourVec.IsLightlike (LeanTT.M74.applyBoostX B ⟨t, t, 0, 0⟩) := by
  apply LeanTT.M74.boostX_preserves_lightcone
  dsimp [LeanTT.M74.FourVec.IsLightlike, LeanTT.M74.FourVec.intervalSq, LeanTT.M74.FourVec.minkowskiDot]
  omega

/-- EJERCICIO 4 (Acción de Hadamard sobre $\lvert 1\rangle$):
    Demuestra que aplicar la puerta de Hadamard escalada `hadamardScaled` al estado $\lvert 1\rangle$
    produce el estado de fase opuesta $\lvert -\rangle = \lvert 0\rangle - \lvert 1\rangle$. -/
theorem ej4_hadamard_ket1_eq_ketMinus :
    LeanTT.M76.applyMat2 LeanTT.M77.hadamardScaled LeanTT.M76.ket1 = LeanTT.M76.ketMinus := by
  decide

/-- EJERCICIO 5 (Involutividad Simbólica de Hadamard en Gottesman-Knill):
    Demuestra que conjugar dos veces cualquier operador de Pauli con signo `sp` mediante el
    generador de Clifford `.H` devuelve exactamente `sp` (`H (H P H) H = P`). -/
theorem ej5_gottesman_knill_double_H (sp : LeanTT.M80.SignedPauli) :
    LeanTT.M80.conjugatePauliSymbolic .H (LeanTT.M80.conjugatePauliSymbolic .H sp) = sp := by
  cases sp with | mk neg sym =>
  cases neg <;> cases sym <;> rfl

end LeanTT.Exercises.E06
