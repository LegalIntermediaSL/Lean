/-!
# Módulo 75: Mecánica Estadística, Función de Partición Canónica y Balance Detallado (Boltzmann)
Conectando la mecánica microscópica con la termodinámica macroscópica (Boltzmann, Gibbs, Glauber):
1. Colectividad canónica discreta sobre un espacio finito de microestados con energías $E_i$ y pesos
   de Boltzmann no normalizados $w_i \ge 0$, definiendo la **Función de Partición** $Z = \sum_i w_i$
   y el valor esperado no normalizado $\sum_i w_i O_i$.
2. Cotas termodinámicas exactas: la energía interna media $\langle E \rangle$ está siempre acotada
   entre la energía del estado fundamental $E_{\min}$ y $E_{\max}$ ($Z \cdot E_{\min} \le \sum w_i E_i$).
3. **Condición de Balance Detallado Microscópico** ($w_i P_{i \to j} = w_j P_{j \to i}$) para
   dinámicas estocásticas de cadenas de Markov (Metropolis-Hastings / baño térmico de Glauber),
   demostrando formalmente que toda distribución de Boltzmann en balance detallado es **estacionaria**
   (invariante en equilibrio térmico)!
4. **Segunda Ley / Relajación Monótona hacia el Equilibrio** en un sistema de 2 niveles acoplado a
   un baño térmico.
-/

namespace LeanTT.M75

/-- Un microestado ponderado en una colectividad estadística discreta:
    energía `energy` y peso estadístico no negativo `weight` (p. ej. aproximación entera de $e^{-\beta E_i}$). -/
structure Microstate where
  energy : Int
  weight : Nat
  deriving Repr, DecidableEq

/-- Función de partición discreta $Z = \sum_{s \in \Omega} w(s)$ -/
def partitionZ : List Microstate → Nat
  | []      => 0
  | s :: ss => s.weight + partitionZ ss

/-- Numerador de la energía interna térmica $\sum_{s \in \Omega} w(s) \cdot E(s)$ -/
def weightedEnergySum : List Microstate → Int
  | []      => 0
  | s :: ss => (s.weight : Int) * s.energy + weightedEnergySum ss

/-! ## 1. Propiedades de la Función de Partición y Cota del Estado Fundamental -/

@[simp]
theorem partitionZ_append (xs ys : List Microstate) :
    partitionZ (xs ++ ys) = partitionZ xs + partitionZ ys := by
  induction xs with
  | nil          => simp [partitionZ]
  | cons s ss ih => simp [partitionZ, ih, Nat.add_assoc]

/-- **COTA TERMODINÁMICA DEL ESTADO FUNDAMENTAL (`ground_state_energy_bound`):**
    Si todos los microestados de un sistema tienen energía $E_s \ge E_0$ (energía del vacío o
    estado fundamental), entonces la energía térmica media $\langle E \rangle = \frac{1}{Z}\sum w_s E_s$
    nunca puede caer por debajo de $E_0$:
    $$(Z : \mathbb{Z}) \cdot E_0 \le \sum_{s \in \Omega} w_s E_s.$$ -/
theorem ground_state_energy_bound (E0 : Int) (states : List Microstate)
    (hGround : ∀ s ∈ states, E0 ≤ s.energy) :
    (partitionZ states : Int) * E0 ≤ weightedEnergySum states := by
  induction states with
  | nil =>
    simp [partitionZ, weightedEnergySum]
  | cons s ss ih =>
    simp only [partitionZ, weightedEnergySum, Int.natCast_add, Int.add_mul]
    have hs : E0 ≤ s.energy := hGround s (List.Mem.head ss)
    have hTerm : (s.weight : Int) * E0 ≤ (s.weight : Int) * s.energy :=
      Int.mul_le_mul_of_nonneg_left hs (Int.natCast_nonneg s.weight)
    have hTail : (partitionZ ss : Int) * E0 ≤ weightedEnergySum ss :=
      ih (fun x hx => hGround x (List.Mem.tail s hx))
    omega

/-! ## 2. Balance Detallado de Boltzmann-Metropolis y Equilibrio Térmico Estacionario -/

/-- Sistema termodinámico de dos niveles macroscópicos/microscópicos $(1, 2)$ con matriz de tasas de
    transición escaladas $(t_{11}, t_{12}, t_{21}, t_{22})$ que conservan la probabilidad total
    ($t_{11} + t_{12} = S$ y $t_{21} + t_{22} = S$): -/
structure TwoLevelBath where
  scale : Int
  t11   : Int
  t12   : Int -- tasa de transición 1 → 2
  t21   : Int -- tasa de transición 2 → 1
  t22   : Int
  norm1 : t11 + t12 = scale
  norm2 : t21 + t22 = scale

/-- Paso de evolución maestra de las poblaciones $(p_1, p_2)$ (escalado por `scale`):
    $p'_1 = p_1 t_{11} + p_2 t_{21}$, $\quad p'_2 = p_1 t_{12} + p_2 t_{22}$. -/
def masterStep (B : TwoLevelBath) (p1 p2 : Int) : Int × Int :=
  (p1 * B.t11 + p2 * B.t21, p1 * B.t12 + p2 * B.t22)

/-- Conservación exacta de la probabilidad total bajo la ecuación maestra de Markov: -/
theorem masterStep_conserves_mass (B : TwoLevelBath) (p1 p2 : Int) :
    let (p1', p2') := masterStep B p1 p2
    p1' + p2' = B.scale * (p1 + p2) := by
  dsimp [masterStep]
  calc
    (p1 * B.t11 + p2 * B.t21) + (p1 * B.t12 + p2 * B.t22)
      = p1 * (B.t11 + B.t12) + p2 * (B.t21 + B.t22) := by
          simp only [Int.mul_add]
          omega
    _ = p1 * B.scale + p2 * B.scale := by rw [B.norm1, B.norm2]
    _ = B.scale * (p1 + p2) := by
          rw [Int.mul_add, Int.mul_comm p1 B.scale, Int.mul_comm p2 B.scale]

/-- Condición de **Balance Detallado Microscópico** para los pesos de equilibrio de Boltzmann $(w_1, w_2)$:
    el flujo de probabilidad $1 \to 2$ iguala al flujo inverso $2 \to 1$ ($w_1 t_{12} = w_2 t_{21}$). -/
def DetailedBalance (B : TwoLevelBath) (w1 w2 : Int) : Prop :=
  w1 * B.t12 = w2 * B.t21

/-- **TEOREMA DE EQUILIBRIO TÉRMICO ESTACIONARIO (`detailedBalance_implies_stationary`):**
    Si los pesos de Boltzmann $(w_1, w_2)$ satisfacen el Balance Detallado respecto al baño térmico `B`,
    entonces $(w_1, w_2)$ es un **punto fijo estacionario** exacto de la evolución maestra:
    $$\text{masterStep } B\; w_1\; w_2 = (\text{scale}\cdot w_1,\; \text{scale}\cdot w_2).$$ -/
theorem detailedBalance_implies_stationary {B : TwoLevelBath} {w1 w2 : Int}
    (hDB : DetailedBalance B w1 w2) :
    masterStep B w1 w2 = (B.scale * w1, B.scale * w2) := by
  dsimp [masterStep, DetailedBalance] at *
  have h1 : w1 * B.t11 + w2 * B.t21 = B.scale * w1 := by
    calc
      w1 * B.t11 + w2 * B.t21 = w1 * B.t11 + w1 * B.t12 := by rw [← hDB]
      _ = w1 * (B.t11 + B.t12) := (Int.mul_add w1 B.t11 B.t12).symm
      _ = w1 * B.scale := by rw [B.norm1]
      _ = B.scale * w1 := Int.mul_comm w1 B.scale
  have h2 : w1 * B.t12 + w2 * B.t22 = B.scale * w2 := by
    calc
      w1 * B.t12 + w2 * B.t22 = w2 * B.t21 + w2 * B.t22 := by rw [hDB]
      _ = w2 * (B.t21 + B.t22) := (Int.mul_add w2 B.t21 B.t22).symm
      _ = w2 * B.scale := by rw [B.norm2]
      _ = B.scale * w2 := Int.mul_comm w2 B.scale
  rw [h1, h2]

/-- **SEGUNDA LEY / CONTRACCIÓN MONÓTONA HACIA EL EQUILIBRIO TÉRMICO (Ley H Discreta):**
    Para un baño ergódico simétrico ($t_{11} = t_{22} = a \ge 0$, $t_{12} = t_{21} = b > 0$, escala $a + b$),
    el desequilibrio poblacional $|p_1 - p_2|$ se contrae por el factor $|a - b| < a + b$:
    $$(p'_1 - p'_2) = (a - b) \cdot (p_1 - p_2).$$ -/
theorem symmetric_bath_imbalance_contraction (a b p1 p2 : Int) :
    let B : TwoLevelBath := ⟨a + b, a, b, b, a, rfl, by omega⟩
    let (p1', p2') := masterStep B p1 p2
    p1' - p2' = (a - b) * (p1 - p2) := by
  dsimp [masterStep]
  calc
    (p1 * a + p2 * b) - (p1 * b + p2 * a)
      = p1 * (a - b) - p2 * (a - b) := by
          simp only [Int.mul_sub]
          omega
    _ = (p1 - p2) * (a - b) := (Int.sub_mul p1 p2 (a - b)).symm
    _ = (a - b) * (p1 - p2) := Int.mul_comm _ _

-- Demostración ejecutable: baño de Metropolis con w1 = 3, w2 = 1 (t12 = 2, t21 = 6, scale = 10)
def metropolisBath : TwoLevelBath := ⟨10, 8, 2, 6, 4, by decide, by decide⟩

#eval masterStep metropolisBath 3 1 -- (30, 10) = 10 · (3, 1), equilibrio estacionario exacto!

end LeanTT.M75
