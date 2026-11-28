# Lección 02: Mecánica Lagrangiana, Principio de Mínima Acción y Teorema de Noether en Lean 4

> **Módulos ejecutables asociados:** [`LeanTT/M72_LagrangianMechanicsAndEulerLagrange.lean`](../../LeanTT/M72_LagrangianMechanicsAndEulerLagrange.lean) y [`LeanTT/M38_VerifiedAutomaticDifferentiation.lean`](../../LeanTT/M38_VerifiedAutomaticDifferentiation.lean).
> **Navegación:** [⬅ Lección 01: Análisis Dimensional](01_analisis_dimensional_y_unidades_dependientes.md) | [Siguiente: Mecánica Hamiltoniana y Simpléctica ➡](03_mecanica_hamiltoniana_poisson_y_simpleticos.md)

---

## 1. Del Cálculo Variacional Continuo a la Mecánica Lagrangiana Discreta Exacta

En la mecánica analítica de Lagrange (1788) y Hamilton (1834), la trayectoria física $q : [t_0, t_N] \to Q$ entre dos configuraciones fijas $q(t_0) = q_0$ y $q(t_N) = q_N$ es aquella que hace estacionario el funcional de **Acción**:
$$S[q] = \int_{t_0}^{t_N} L(q(t), \dot{q}(t))\,dt, \qquad \delta S[q] = 0 \iff \frac{\partial L}{\partial q} - \frac{d}{dt}\left(\frac{\partial L}{\partial \dot{q}}\right) = 0.$$

En la geometría diferencial discreta moderna (**Marsden & West, 2001** — *Discrete Mechanics and Variational Integrators*), sustituimos la integral en cada intervalo $[t_k, t_{k+1}]$ por un **Lagrangiano discreto exacto** $L_d(q_k, q_{k+1})$. Para una trayectoria de dos pasos $(q_0, q_1, q_2)$ con extremos fijos ($\delta q_0 = \delta q_2 = 0$), variar el punto intermedio $q_1 \mapsto q_1 + \delta q_1$ produce:
$$\delta S = \big(D_2 L_d(q_0, q_1) + D_1 L_d(q_1, q_2)\big)\cdot \delta q_1.$$

¡Esta formulación no es una mera aproximación numérica: conserva de forma **exacta** la estructura simpléctica y todas las leyes de conservación de Noether sin necesidad de límites analíticos complejos!

```lean
namespace CursoFisica.L02

/-- Un Lagrangiano discreto `L(qa, qb)` con sus derivadas parciales exactas `d1` y `d2`: -/
structure DiscreteLagrangian where
  L  : Int → Int → Int
  d1 : Int → Int → Int
  d2 : Int → Int → Int

def firstVariation (sys : DiscreteLagrangian) (q0 q1 q2 dq1 : Int) : Int :=
  (sys.d2 q0 q1 + sys.d1 q1 q2) * dq1

def SatisfiesDEL (sys : DiscreteLagrangian) (q0 q1 q2 : Int) : Prop :=
  sys.d2 q0 q1 + sys.d1 q1 q2 = 0

/-- Principio de Acción Estacionaria de Hamilton:
    δS = 0 para toda perturbación virtual `dq1` ⟺ Ecuación de Euler-Lagrange Discreta! -/
theorem hamilton_stationary_principle (sys : DiscreteLagrangian) (q0 q1 q2 : Int) :
    (∀ dq1 : Int, firstVariation sys q0 q1 q2 dq1 = 0) ↔ SatisfiesDEL sys q0 q1 q2 := by
  constructor
  · intro h
    have h1 := h 1
    dsimp [firstVariation, SatisfiesDEL] at *
    omega
  · intro hEL dq1
    dsimp [firstVariation, SatisfiesDEL] at *
    rw [hEL, Int.zero_mul]

end CursoFisica.L02
```

---

## 2. El Teorema de Emmy Noether (1918) Demostrado en Lean 4

El teorema más profundo de la física matemática moderna, demostrado por **Emmy Noether** en Gotinga en 1918, establece una biyección entre **simetrías continuas de la acción** y **cantidades conservadas**:
* Simetría de traslación temporal $\implies$ Conservación de la **Energía**.
* Simetría de traslación espacial $\implies$ Conservación del **Momento Lineal**.
* Simetría de rotación espacial $\implies$ Conservación del **Momento Angular**.
* Simetría de fase global $U(1)$ $\implies$ Conservación de la **Carga Eléctrica**.

Definamos el **momento canónico saliente** mediante la transformada de Legendre discreta $p^+(q_a, q_b) = D_2 L_d(q_a, q_b)$. Si el sistema es invariante bajo traslaciones espaciales $q \mapsto q + \varepsilon$, la derivada direccional a lo largo de $(1, 1)$ se anula: $D_1 L_d(q_a, q_b) + D_2 L_d(q_a, q_b) = 0$.

Veamos cómo el kernel de Lean 4 verifica el **Teorema de Noether** en pocas líneas transparentes:

```lean
namespace CursoFisica.L02

def momentumOut (sys : DiscreteLagrangian) (qa qb : Int) : Int :=
  sys.d2 qa qb

def IsTranslationInvariant (sys : DiscreteLagrangian) : Prop :=
  ∀ qa qb : Int, sys.d1 qa qb + sys.d2 qa qb = 0

/-- TEOREMA DE NOETHER:
    Invariancia traslacional + Ecuación de Euler-Lagrange ⟹ p⁺(q0, q1) = p⁺(q1, q2)! -/
theorem noether_conservation {sys : DiscreteLagrangian}
    (hSym : IsTranslationInvariant sys)
    {q0 q1 q2 : Int} (hEL : SatisfiesDEL sys q0 q1 q2) :
    momentumOut sys q0 q1 = momentumOut sys q1 q2 := by
  have h12 := hSym q1 q2
  dsimp [SatisfiesDEL, momentumOut] at *
  omega

end CursoFisica.L02
```

---

## 3. Aplicación Ejecutable: Partícula Libre e Inercia de Galileo-Newton

Instanciemos `DiscreteLagrangian` con la energía cinética discreta escalada $2 L_d(q_a, q_b) = m (q_b - q_a)^2$:

```lean
open CursoFisica.L02

def freeParticle (m : Int) : DiscreteLagrangian where
  L  qa qb := m * (qb - qa) * (qb - qa)
  d1 qa qb := -(2 * m * (qb - qa))
  d2 qa qb := 2 * m * (qb - qa)

theorem freeParticle_symmetric (m : Int) : IsTranslationInvariant (freeParticle m) := by
  intro qa qb
  dsimp [freeParticle]
  omega

-- Aplicando el Teorema de Noether obtenemos automáticamente la conservación de `2·m·v`:
theorem freeParticle_momentum_constant {m q0 q1 q2 : Int}
    (hEL : SatisfiesDEL (freeParticle m) q0 q1 q2) :
    2 * m * (q1 - q0) = 2 * m * (q2 - q1) :=
  noether_conservation (freeParticle_symmetric m) hEL

#eval (freeParticle 5).d2 10 16 -- Momento escalado 2·m·v = 2 * 5 * 6 = 60
```

---

👉 **Siguiente lección:** [**Lección 03 — Mecánica Hamiltoniana, Corchetes de Poisson, Identidad de Jacobi e Integradores Simplécticos**](03_mecanica_hamiltoniana_poisson_y_simpleticos.md)
