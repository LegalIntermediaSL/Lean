import LeanTT.M61_QuantitativeTypeTheoryQTT
import LeanTT.M62_PostQuantumLatticeCryptoLWE
import LeanTT.M63_VerifiedNeuralNetworkReLURobustness
import LeanTT.M65_ConflictFreeReplicatedDataTypesCRDT
import LeanTT.M66_ReversibleAndQuantumGateLogic
import LeanTT.M69_VerifiedHardwareAdderAndALU

/-!
# Taller de Ejercicios 05: QTT, Criptografía Post-Cuántica LWE, Redes Neuronales ReLU, CRDTs y Hardware
Soluciones comentadas disponibles en: `LeanTT/Solutions/S05_WorkoutQTTPostQuantumAndHardware.lean`

En este quinto taller práctico aplicamos las técnicas de los módulos `M61`–`M70`:
1. Escalado de contextos lineales en Quantitative Type Theory (QTT).
2. Desencriptado post-cuántico LWE con ruido nulo (`e = 0`).
3. Puntos fijos de la función de activación `ReLU`.
4. Conmutatividad de circuitos sumadores de hardware (*Full-Adder*).
-/

namespace LeanTT.Exercises.E05

/-- EJERCICIO 1 (Identidad de Escalado Lineal en QTT):
    Demuestra que escalar un contexto de multiplicidades `Γ : List Mult` por la multiplicidad
    lineal `.one` (`1`) deja el contexto exactamente intacto (`scaleCtx .one Γ = Γ`). -/
theorem ej1_scaleCtx_one_id (Γ : List LeanTT.M61.Mult) :
    LeanTT.M61.Mult.scaleCtx .one Γ = Γ := by
  induction Γ with
  | nil          => rfl
  | cons m ms ih =>
    cases m <;> simp [LeanTT.M61.Mult.scaleCtx, ih]

/-- EJERCICIO 2 (Cifrado LWE Sin Ruido):
    Usando `lwe_decrypt_correct` del Módulo 62, demuestra que si `0 < K` y el ruido es `e = 0`,
    el desencriptado LWE recupera exactamente el bit original `m : Bool`. -/
theorem ej2_lwe_noiseless_decrypt (K s a : Int) (m : Bool) (hK : 0 < K) :
    LeanTT.M62.lweDecrypt K s a (LeanTT.M62.lweEncrypt K s a 0 m) = m := by
  apply LeanTT.M62.lwe_decrypt_correct
  · omega
  · omega

/-- EJERCICIO 3 (Caracterización de Puntos Fijos Positivos de `ReLU`):
    Demuestra que para toda entrada no negativa `0 ≤ x`, la función de activación `relu x`
    actúa como la identidad (`relu x = x`). -/
theorem ej3_relu_eq_self_of_nonneg {x : Int} (h : 0 ≤ x) :
    LeanTT.M63.relu x = x := by
  dsimp [LeanTT.M63.relu]
  split <;> omega

/-- EJERCICIO 4 (Simetría de las Entradas `a` y `b` en un *Full-Adder* de Hardware):
    Demuestra que intercambiar los cables de entrada `a` y `b` en un sumador completo de 1 bit
    produce exactamente el mismo bit de suma y el mismo bit de acarreo (`fullAdder a b cin = fullAdder b a cin`). -/
theorem ej4_fullAdder_comm_ab (a b cin : Bool) :
    LeanTT.M69.fullAdder a b cin = LeanTT.M69.fullAdder b a cin := by
  cases a <;> cases b <;> cases cin <;> rfl

end LeanTT.Exercises.E05
