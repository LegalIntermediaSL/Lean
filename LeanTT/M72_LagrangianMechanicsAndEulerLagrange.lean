/-!
# Módulo 72: Mecánica Lagrangiana, Cálculo Variacional Discreto y Teorema de Noether
Inspirado en la formulación variacional de Marsden-West (*Discrete Mechanics and Variational
Integrators*) y en **SciLean / PhysLean**:

En lugar de postular $F = ma$ ad hoc, toda la física fundamental moderna (desde la mecánica clásica
hasta el Modelo Estándar) deriva las ecuaciones de movimiento del **Principio de Acción Estacionaria
de Hamilton** ($\delta S[q] = 0$).

En este módulo formalizamos de manera 100% constructiva y ejecutable:
1. Lagrangianos discretos diferenciables $L_d(q_k, q_{k+1})$ con sus derivadas parciales exactas
   $D_1 L_d$ y $D_2 L_d$ (estilo números duales del Módulo 38).
2. La **Primera Variación de la Acción** en 2 pasos con extremos fijos ($\delta q_0 = \delta q_2 = 0$),
   demostrando formalmente que la acción es estacionaria al primer orden ($\delta S = 0$ para todo
   $\delta q_1$) **si y solo si** se satisface la **Ecuación de Euler-Lagrange Discreta (DEL)**:
   $$D_2 L_d(q_0, q_1) + D_1 L_d(q_1, q_2) = 0.$$
3. **Teorema de Noether Discreto:** si el Lagrangiano es invariante bajo traslaciones espaciales
   infinitesimales ($D_1 L_d(q_a, q_b) + D_2 L_d(q_a, q_b) = 0$), entonces el **momento canónico
   conjugado** $p_k = D_2 L_d(q_{k-1}, q_k)$ **se conserva exactamente** a lo largo de cualquier
   trayectoria de Euler-Lagrange!
4. Instanciación verificada para la **partícula libre** y el **oscilador armónico**.
-/

namespace LeanTT.M72

/-- Especificación de un Lagrangiano discreto de 1 paso $L_d(q_a, q_b)$ equipado con sus dos
    derivadas parciales exactas $D_1 L_d = \frac{\partial L_d}{\partial q_a}$ y
    $D_2 L_d = \frac{\partial L_d}{\partial q_b}$. -/
structure DiscreteLagrangian where
  L  : Int → Int → Int
  d1 : Int → Int → Int
  d2 : Int → Int → Int

/-- Acción total de un camino de dos intervalos $(q_0, q_1, q_2)$:
    $S(q_0, q_1, q_2) = L_d(q_0, q_1) + L_d(q_1, q_2)$. -/
def action2 (sys : DiscreteLagrangian) (q0 q1 q2 : Int) : Int :=
  sys.L q0 q1 + sys.L q1 q2

/-- Variación lineal de primer orden $\delta S$ respecto a una perturbación interior $\delta q_1$
    con extremos fijos ($\delta q_0 = 0, \delta q_2 = 0$): -/
def firstVariation2 (sys : DiscreteLagrangian) (q0 q1 q2 dq1 : Int) : Int :=
  (sys.d2 q0 q1 + sys.d1 q1 q2) * dq1

/-- Predicado de solución de la **Ecuación de Euler-Lagrange Discreta (DEL)** en el nodo interior $q_1$: -/
def SatisfiesDEL (sys : DiscreteLagrangian) (q0 q1 q2 : Int) : Prop :=
  sys.d2 q0 q1 + sys.d1 q1 q2 = 0

/-- Momento canónico discreto entrante/saliente definido mediante la transformada de Legendre discreta:
    $p^+(q_0, q_1) = D_2 L_d(q_0, q_1)$ y $p^-(q_1, q_2) = - D_1 L_d(q_1, q_2)$. -/
def canonicalMomentumOut (sys : DiscreteLagrangian) (qa qb : Int) : Int :=
  sys.d2 qa qb

def canonicalMomentumIn (sys : DiscreteLagrangian) (qa qb : Int) : Int :=
  -(sys.d1 qa qb)

/-! ## 1. Principio de Hamilton: Acción Estacionaria $\iff$ Ecuaciones de Euler-Lagrange -/

/-- TEOREMA FUNDAMENTAL DEL CÁLCULO VARIACIONAL DISCRETO (Lema Fundamental de Lagrange):
    La primera variación $\delta S(q_0, q_1, q_2; \delta q_1)$ se anula para **toda** perturbación
    virtual $\delta q_1 \in \mathbb{Z}$ si y solo si la trayectoria $(q_0, q_1, q_2)$ satisface la
    Ecuación de Euler-Lagrange Discreta `SatisfiesDEL`. -/
theorem stationary_action_iff_euler_lagrange (sys : DiscreteLagrangian) (q0 q1 q2 : Int) :
    (∀ dq1 : Int, firstVariation2 sys q0 q1 q2 dq1 = 0) ↔ SatisfiesDEL sys q0 q1 q2 := by
  constructor
  · intro hAll
    have h1 := hAll 1
    dsimp [firstVariation2, SatisfiesDEL] at *
    omega
  · intro hDEL dq1
    dsimp [firstVariation2, SatisfiesDEL] at *
    rw [hDEL, Int.zero_mul]

/-- Equivalencia de Legendre: las ecuaciones de Euler-Lagrange coinciden exactamente con el
    emparejamiento de momentos canónicos $p^+(q_0, q_1) = p^-(q_1, q_2)$. -/
theorem euler_lagrange_iff_momentum_matching (sys : DiscreteLagrangian) (q0 q1 q2 : Int) :
    SatisfiesDEL sys q0 q1 q2 ↔
      canonicalMomentumOut sys q0 q1 = canonicalMomentumIn sys q1 q2 := by
  dsimp [SatisfiesDEL, canonicalMomentumOut, canonicalMomentumIn]
  omega

/-! ## 2. Teorema de Noether Formalizado: Simetría Continua $\implies$ Ley de Conservación -/

/-- Condición infinitesimal de **Simetría de Traslación** del Lagrangiano:
    desplazar simultáneamente ambos puntos $q_a \mapsto q_a + \varepsilon, q_b \mapsto q_b + \varepsilon$
    no altera el Lagrangiano al primer orden ($D_1 L_d(q_a, q_b) + D_2 L_d(q_a, q_b) = 0$). -/
def IsTranslationSymmetric (sys : DiscreteLagrangian) : Prop :=
  ∀ qa qb : Int, sys.d1 qa qb + sys.d2 qa qb = 0

/-- **TEOREMA DE EMMY NOETHER (1918) — Versión Variacional Exacta:**
    Si el Lagrangiano `sys` posee simetría de traslación (`IsTranslationSymmetric sys`) y
    la trayectoria `(q0, q1, q2)` satisface las ecuaciones de Euler-Lagrange (`SatisfiesDEL`),
    entonces el **momento canónico se conserva exactamente de un paso al siguiente**:
    $$p^+(q_0, q_1) = p^+(q_1, q_2).$$ -/
theorem noether_momentum_conservation
    {sys : DiscreteLagrangian}
    (hSym : IsTranslationSymmetric sys)
    {q0 q1 q2 : Int}
    (hEL : SatisfiesDEL sys q0 q1 q2) :
    canonicalMomentumOut sys q0 q1 = canonicalMomentumOut sys q1 q2 := by
  have hLocalSym := hSym q1 q2
  dsimp [SatisfiesDEL, canonicalMomentumOut] at *
  omega

/-! ## 3. Sistemas Físicos Concretos: Partícula Libre y Oscilador Armónico -/

/-- Lagrangiano discreto escalado ($\times 2$, con $\Delta t = 1$) de una partícula libre de masa $m$:
    $2 L_d(q_a, q_b) = m (q_b - q_a)^2$, con derivadas exactas:
    $D_1(2 L_d) = -2 m (q_b - q_a)$ y $D_2(2 L_d) = 2 m (q_b - q_a)$. -/
def freeParticle (m : Int) : DiscreteLagrangian where
  L  qa qb := m * (qb - qa) * (qb - qa)
  d1 qa qb := -(2 * m * (qb - qa))
  d2 qa qb := 2 * m * (qb - qa)

/-- Demostración formal de que la partícula libre es invariante bajo traslaciones espaciales: -/
theorem freeParticle_translation_symmetric (m : Int) :
    IsTranslationSymmetric (freeParticle m) := by
  intro qa qb
  dsimp [freeParticle]
  omega

/-- Por el Teorema de Noether, toda trayectoria de Euler-Lagrange de una partícula libre conserva
    exactamente su momento lineal $2 m (q_1 - q_0) = 2 m (q_2 - q_1)$ (1.ª Ley de Inercia de Newton!): -/
theorem freeParticle_conserves_momentum {m q0 q1 q2 : Int}
    (hEL : SatisfiesDEL (freeParticle m) q0 q1 q2) :
    2 * m * (q1 - q0) = 2 * m * (q2 - q1) :=
  noether_momentum_conservation (freeParticle_translation_symmetric m) hEL

/-- Oscilador armónico discreto ($2 L_d(q_a, q_b) = m (q_b - q_a)^2 - k q_a^2$):
    satisface la ecuación en diferencias de segundo orden $2 m (q_2 - 2 q_1 + q_0) = - 2 k q_1$
    (Ley de Hooke $m \ddot{q} = - k q$!). -/
def harmonicOscillator (m k : Int) : DiscreteLagrangian where
  L  qa qb := m * (qb - qa) * (qb - qa) - k * qa * qa
  d1 qa qb := -(2 * m * (qb - qa)) - 2 * k * qa
  d2 qa qb := 2 * m * (qb - qa)

theorem harmonicOscillator_euler_lagrange_eq (m k q0 q1 q2 : Int) :
    SatisfiesDEL (harmonicOscillator m k) q0 q1 q2 ↔
      2 * m * (q2 - 2 * q1 + q0) = -(2 * k * q1) := by
  dsimp [SatisfiesDEL, harmonicOscillator]
  constructor <;> intro h
  · have hLin : 2 * m * (q1 - q0) + (-(2 * m * (q2 - q1)) - 2 * k * q1) =
                -(2 * m * (q2 - 2 * q1 + q0)) - 2 * k * q1 := by
      have hSub : (q1 - q0) - (q2 - q1) = -(q2 - 2 * q1 + q0) := by omega
      calc
        2 * m * (q1 - q0) + (-(2 * m * (q2 - q1)) - 2 * k * q1)
          = 2 * m * (q1 - q0) - 2 * m * (q2 - q1) - 2 * k * q1 := by omega
        _ = 2 * m * ((q1 - q0) - (q2 - q1)) - 2 * k * q1 := by rw [← Int.mul_sub]
        _ = -(2 * m * (q2 - 2 * q1 + q0)) - 2 * k * q1 := by rw [hSub, Int.mul_neg]
    omega
  · have hLin : 2 * m * (q1 - q0) - 2 * m * (q2 - q1) = -(2 * m * (q2 - 2 * q1 + q0)) := by
      have hSub : (q1 - q0) - (q2 - q1) = -(q2 - 2 * q1 + q0) := by omega
      rw [← Int.mul_sub, hSub, Int.mul_neg]
    omega

-- Evaluación ejecutable: trayectoria inercial q = (10, 17, 24) con velocidad constante v = 7 y m = 3
#eval action2 (freeParticle 3) 10 17 24
#eval canonicalMomentumOut (freeParticle 3) 10 17

end LeanTT.M72
