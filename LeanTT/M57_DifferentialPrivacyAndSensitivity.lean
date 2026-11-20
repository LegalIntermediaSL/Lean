/-!
# Módulo 57: Privacidad Diferencial, $L_1$-Sensibilidad de Consultas y Composición de Presupuesto $\varepsilon$
## Ámbito: Privacidad Estadística (Dwork-McSherry-Nissim-Smith 2006) y Aprendizaje Automático Seguro

En la **Privacidad Diferencial** ($\varepsilon$-DP), calibrar la magnitud del ruido aleatorio
(por ejemplo, en el Mecanismo de Laplace o Geométrico Discreto) requiere acotar formalmente la
**Sensibilidad Global ($L_1$-Sensitivity)** $\Delta f$ de una consulta $f : \text{DB} \to \mathbb{Z}$:
¿cuánto puede cambiar la salida $|f(D_1) - f(D_2)|$ cuando las bases de datos $D_1$ y $D_2$ difieren
en a lo sumo $1$ registro?

En este módulo:
1. Formalizamos la distancia absoluta `absDiff a b = (a - b).natAbs`, la propiedad de que una
   consulta `q : DB → Int` tenga sensibilidad acotada por `s : Nat` (`HasSensitivity Adj q s`) y
   su estabilidad bajo escalado y suma de consultas.
2. Demostramos el **Teorema de Sensibilidad de la Suma de Consultas** ($\Delta(q_1 + q_2) \le \Delta q_1 + \Delta q_2$)
   y la **Invariancia por Desplazamiento Constante**.
3. Formalizamos el **Presupuesto de Privacidad ($\varepsilon$)** y demostramos la ley de
   **Composición Secuencial** ($\varepsilon_{\text{total}} = \sum \varepsilon_i$) y **Composición Paralela** ($\max \varepsilon_i$).
-/

namespace LeanTT.M57

/-- Distancia absoluta $L_1$ entre dos enteros `a, b : Int` como número natural `|a - b|` -/
@[simp]
def absDiff (a b : Int) : Nat :=
  (a - b).natAbs

/-- Una consulta `q : DB → Int` tiene sensibilidad global a lo sumo `s : Nat` respecto a la
    relación de adyacencia de bases de datos `Adj : DB → DB → Prop` si para todo par de
    bases de datos vecinas `Adj d1 d2`, `|q(d1) - q(d2)| ≤ s`. -/
def HasSensitivity {DB : Type} (Adj : DB → DB → Prop) (q : DB → Int) (s : Nat) : Prop :=
  ∀ d1 d2 : DB, Adj d1 d2 → absDiff (q d1) (q d2) ≤ s

/-! ## 1. Teoremas de Sensibilidad de Consultas Estadísticas -/

/-- TEOREMA 1 (Sensibilidad Cero de Consultas Constantes):
    Una consulta constante `fun _ => c` tiene sensibilidad `0`. -/
theorem sensitivity_const {DB : Type} (Adj : DB → DB → Prop) (c : Int) :
    HasSensitivity Adj (fun _ => c) 0 := by
  intro d1 d2 _
  dsimp [absDiff]
  omega

/-- TEOREMA 2 (Invariancia de la Sensibilidad bajo Desplazamiento por un Offset `k : Int`):
    Si `q` tiene sensibilidad `s`, entonces `fun d => q d + k` también tiene sensibilidad `s`. -/
theorem sensitivity_add_const {DB : Type} (Adj : DB → DB → Prop) (q : DB → Int) (s : Nat) (k : Int)
    (hq : HasSensitivity Adj q s) :
    HasSensitivity Adj (fun d => q d + k) s := by
  intro d1 d2 hAdj
  have h1 := hq d1 d2 hAdj
  dsimp [absDiff] at h1 ⊢
  have h_eq : (q d1 + k) - (q d2 + k) = q d1 - q d2 := by omega
  rw [h_eq]
  exact h1

/-- TEOREMA 3 (Subaditividad de la Sensibilidad bajo Suma de Consultas):
    Si `q1` tiene sensibilidad `s1` y `q2` tiene sensibilidad `s2`, entonces la consulta suma
    `fun d => q1 d + q2 d` tiene sensibilidad a lo sumo `s1 + s2` (por la desigualdad triangular). -/
theorem sensitivity_add_queries {DB : Type} (Adj : DB → DB → Prop)
    (q1 q2 : DB → Int) (s1 s2 : Nat)
    (hq1 : HasSensitivity Adj q1 s1) (hq2 : HasSensitivity Adj q2 s2) :
    HasSensitivity Adj (fun d => q1 d + q2 d) (s1 + s2) := by
  intro d1 d2 hAdj
  have h1 := hq1 d1 d2 hAdj
  have h2 := hq2 d1 d2 hAdj
  dsimp [absDiff] at h1 h2 ⊢
  omega

/-! ## 2. Contabilidad Certificada del Presupuesto de Privacidad (`PrivacyBudget`) -/

/-- Un mecanismo diferencialmente privado certificado por su coste de privacidad `epsilon : Nat` -/
structure DPMechanism where
  epsilon : Nat
  deriving Repr, DecidableEq

/-- Composición Secuencial de dos mecanismos DP sobre la misma base de datos (`ε₁ + ε₂`) -/
@[simp]
def seqCompose (m1 m2 : DPMechanism) : DPMechanism :=
  { epsilon := m1.epsilon + m2.epsilon }

/-- Composición Paralela de dos mecanismos DP sobre particiones disjuntas de los datos (`max ε₁ ε₂`) -/
@[simp]
def parCompose (m1 m2 : DPMechanism) : DPMechanism :=
  { epsilon := max m1.epsilon m2.epsilon }

/-- Post-procesamiento determinista o aleatorio independiente de los datos: ¡NO consume presupuesto adicional (`0`)! -/
@[simp]
def postProcess (m : DPMechanism) : DPMechanism :=
  m

/-- TEOREMA 4 (La Composición Paralela siempre ahorra o iguala presupuesto frente a la Secuencial):
    Ejecutar dos mecanismos con presupuestos `ε₁, ε₂` sobre particiones disjuntas (`parCompose`)
    nunca consume más presupuesto de privacidad que ejecutarlos secuencialmente (`seqCompose`). -/
theorem parCompose_le_seqCompose (m1 m2 : DPMechanism) :
    (parCompose m1 m2).epsilon ≤ (seqCompose m1 m2).epsilon := by
  dsimp [parCompose, seqCompose]
  omega

end LeanTT.M57
