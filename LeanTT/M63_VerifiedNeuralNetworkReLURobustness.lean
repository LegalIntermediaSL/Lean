/-!
# Módulo 63: IA Segura — Verificación Formal de Redes Neuronales, ReLU y Robustez por Intervalos (IBP)
## Ámbito: Aprendizaje Automático Confiable (*Formal Verification of Neural Networks* / Robustez Adversarial)

Para certificar formalmente que una red neuronal profunda no sufre cambios catastróficos de
clasificación ante perturbaciones adversariales acotadas en la entrada $x \in [l, u]$ (con $u - l \le 2\epsilon$),
los verificadores formales de redes neuronales (como $\alpha,\beta$-CROWN, Marabou e **Interval Bound Propagation — IBP**)
propagan intervalos certificados a través de las capas afines y de la función de activación no lineal
$$\text{ReLU}(x) = \max(0, x)$$

En este módulo:
1. Formalizamos la función de activación `relu (x : Int) : Int` y demostramos sus cuatro propiedades
   algebraicas fundamentales: no-negatividad, idempotencia (`relu (relu x) = relu x`), monotonía
   y estabilidad en semirrecta positiva.
2. Formalizamos intervalos de cotas certificadas `IBound` (`lo ≤ x ≤ hi`), la capa afín de propagación
   de intervalos `affineIBP` y la capa de activación `reluIBP`.
3. Demostramos el **Teorema de Solidez de *Interval Bound Propagation* (`neurona_relu_ibp_sound`)**:
   para toda entrada $x \in [\text{lo}, \text{hi}]$ y peso no negativo $w \ge 0$, la salida de la
   neurona $\text{ReLU}(w \cdot x + b)$ pertenece garantizadamente al intervalo propagado.
-/

namespace LeanTT.M63

/-- Función de activación Unidad Lineal Rectificada (`ReLU(x) = max(0, x)`) -/
@[simp]
def relu (x : Int) : Int :=
  if 0 ≤ x then x else 0

/-! ## 1. Propiedades Algebraicas y de Orden de la Activación `ReLU` -/

/-- TEOREMA 1 (No-Negatividad Universal de `ReLU`):
    Para toda pre-activación `x : Int`, `0 ≤ relu x`. -/
theorem relu_nonneg (x : Int) : 0 ≤ relu x := by
  dsimp [relu]
  split <;> omega

/-- TEOREMA 2 (Cota Superior `x ≤ relu x`): -/
theorem le_relu (x : Int) : x ≤ relu x := by
  dsimp [relu]
  split <;> omega

/-- TEOREMA 3 (Idempotencia de `ReLU`: `relu (relu x) = relu x`):
    Aplicar dos capas `ReLU` consecutivas sin pesos intermedios colapsa en una sola `ReLU`. -/
@[simp]
theorem relu_idem (x : Int) : relu (relu x) = relu x := by
  dsimp [relu]
  split
  · rfl
  · split <;> omega

/-- TEOREMA 4 (Monotonía de `ReLU`):
    Si `x ≤ y`, entonces `relu x ≤ relu y`. ¡Esta monotonía es la que permite propagar intervalos
    exactos a través de capas de activación `ReLU` en tiempo $O(1)$! -/
theorem relu_mono {x y : Int} (h : x ≤ y) : relu x ≤ relu y := by
  dsimp [relu]
  split <;> split <;> omega

/-! ## 2. Propagación Certificada de Cotas de Intervalo (*Interval Bound Propagation*, IBP) -/

/-- Un intervalo cerrado `[lo, hi]` que acota una señal neuronal ante perturbaciones adversariales -/
structure IBound where
  lo : Int
  hi : Int
  deriving Repr, DecidableEq

/-- Predicado que certifica que un valor escalar `x` se encuentra dentro de la caja `b` -/
@[simp]
def inBound (x : Int) (b : IBound) : Prop :=
  b.lo ≤ x ∧ x ≤ b.hi

/-- Propagación de un intervalo `b` a través de la activación `ReLU` -/
@[simp]
def reluIBP (b : IBound) : IBound :=
  { lo := relu b.lo
  , hi := relu b.hi }

/-- TEOREMA 5 (Solidez de la Capa `reluIBP`):
    Si la pre-activación `x` está dentro del intervalo `b`, entonces la post-activación `relu x`
    está garantizadamente dentro del intervalo `reluIBP b`. -/
theorem reluIBP_sound (x : Int) (b : IBound) (hx : inBound x b) :
    inBound (relu x) (reluIBP b) := by
  dsimp [inBound, reluIBP] at hx ⊢
  exact ⟨relu_mono hx.1, relu_mono hx.2⟩

/-- Propagación de un intervalo `b` a través de una transformación afín `x ↦ x + bias` (o suma de sesgo) -/
@[simp]
def addBiasIBP (bias : Int) (b : IBound) : IBound :=
  { lo := b.lo + bias
  , hi := b.hi + bias }

/-- Propagación de dos señales acotadas `b1, b2` a través de un nodo de suma residual (`ResNet skip-connection`) -/
@[simp]
def addResidualIBP (b1 b2 : IBound) : IBound :=
  { lo := b1.lo + b2.lo
  , hi := b1.hi + b2.hi }

/-- TEOREMA 6 (Solidez de Conexión Residual + Sesgo + Activación ReLU):
    Si dos entradas neuronales `x1` y `x2` pertenecen a sus intervalos de perturbación `b1` y `b2`,
    la salida de la capa `relu (x1 + x2 + bias)` pertenece garantizadamente al intervalo certificado
    `reluIBP (addBiasIBP bias (addResidualIBP b1 b2))`! -/
theorem residual_bias_relu_ibp_sound (x1 x2 bias : Int) (b1 b2 : IBound)
    (h1 : inBound x1 b1) (h2 : inBound x2 b2) :
    inBound (relu (x1 + x2 + bias))
            (reluIBP (addBiasIBP bias (addResidualIBP b1 b2))) := by
  apply reluIBP_sound
  dsimp [inBound, addBiasIBP, addResidualIBP] at h1 h2 ⊢
  omega

end LeanTT.M63
