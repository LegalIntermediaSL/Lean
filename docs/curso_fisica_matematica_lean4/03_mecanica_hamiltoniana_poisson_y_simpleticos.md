# Lección 03: Mecánica Hamiltoniana, Corchetes de Poisson, Identidad de Jacobi e Integradores Simplécticos

> **Módulos ejecutables asociados:** [`LeanTT/M73_HamiltonianMechanicsAndPoissonBrackets.lean`](../../LeanTT/M73_HamiltonianMechanicsAndPoissonBrackets.lean) y [`LeanTT/M75_StatisticalMechanicsAndEntropy.lean`](../../LeanTT/M75_StatisticalMechanicsAndEntropy.lean).
> **Navegación:** [⬅ Lección 02: Lagrangiana y Noether](02_mecanica_lagrangiana_accion_y_noether.md) | [Siguiente: Relatividad Especial y Minkowski ➡](04_relatividad_especial_minkowski_y_lorentz.md)

---

## 1. Geometría Simpléctica del Espacio de Fases y Corchetes de Poisson

William Rowan Hamilton (1833) reformuló las ecuaciones de segundo orden de Euler-Lagrange como un sistema simétrico de primer orden sobre el **espacio de fases** $(q, p) \in T^* Q$:
$$\dot{q} = \frac{\partial H}{\partial p}, \qquad \dot{p} = -\frac{\partial H}{\partial q}.$$

La geometría subyacente está gobernada por la **2-forma simpléctica canónica** $\omega = dq \wedge dp$, que asigna a cada par de desplazamientos $(u_q, u_p), (v_q, v_p)$ su área orientada:
$$\omega(u, v) = u_q v_p - u_p v_q,$$
y por el **Corchete de Poisson** $\{F, G\} = \omega(\nabla F, \nabla G) = \partial_q F\,\partial_p G - \partial_p F\,\partial_q G$. En 1925 Paul Dirac descubrió que la cuantización canónica consiste precisamente en reemplazar $\{F, G\} \mapsto \frac{1}{i\hbar}[\hat{F}, \hat{G}]$.

```lean
namespace CursoFisica.L03

structure PhaseVec where
  q : Int
  p : Int
  deriving Repr, DecidableEq

/-- 2-forma simpléctica canónica ω(u, v) = u.q * v.p - u.p * v.q -/
def omegaForm (u v : PhaseVec) : Int :=
  u.q * v.p - u.p * v.q

theorem omegaForm_self (u : PhaseVec) : omegaForm u u = 0 := by
  dsimp [omegaForm]
  rw [Int.mul_comm u.q u.p]
  omega

theorem omegaForm_skew (u v : PhaseVec) : omegaForm u v = - omegaForm v u := by
  dsimp [omegaForm]
  rw [Int.mul_comm v.q u.p, Int.mul_comm v.p u.q]
  omega

end CursoFisica.L03
```

---

## 2. Por Qué Falla Euler Explícito en Órbitas Planetarias y Cómo Lo Resuelve el Teorema de Liouville Simpléctico

Supongamos que integramos numéricamente un planeta o un oscilador armónico ($\dot{q} = \alpha p$, $\dot{p} = -\kappa q$):
* **Método de Euler explícito ingenuo:** $q_{n+1} = q_n + \alpha p_n$, $p_{n+1} = p_n - \kappa q_n$. El determinante jacobiano vale $\det J = 1 + \alpha\kappa > 1$: ¡en cada paso de tiempo el área del espacio de fases **se infla artificialmente** y la órbita espiralea hacia fuera ganando energía de la nada!
* **Método de Euler Simpléctico y Leapfrog (Störmer-Verlet):** actualizamos primero el momento $p_{n+1} = p_n - \kappa q_n$ y usamos inmediatamente el **nuevo** momento $p_{n+1}$ para avanzar la posición $q_{n+1} = q_n + \alpha p_{n+1}$.

Demostremos en Lean 4 que el integrador simpléctico satisface **exactamente** el **Teorema de Liouville Discreto** ($\omega(\Phi(u), \Phi(v)) = \omega(u, v)$) y que **Störmer-Verlet** es **exactamente reversible en el tiempo**:

```lean
open CursoFisica.L03

def symplecticEuler (α κ : Int) (s : PhaseVec) : PhaseVec :=
  let p1 := s.p - κ * s.q
  let q1 := s.q + α * p1
  ⟨q1, p1⟩

/-- TEOREMA DE LIOUVILLE DISCRETO: Preservación exacta del área simpléctica en cada paso! -/
theorem liouville_symplectic_preservation (α κ : Int) (u v : PhaseVec) :
    omegaForm (symplecticEuler α κ u) (symplecticEuler α κ v) = omegaForm u v := by
  cases u with | mk uq up =>
  cases v with | mk vq vp =>
  dsimp [symplecticEuler, omegaForm]
  calc
    (uq + α * (up - κ * uq)) * (vp - κ * vq) - (up - κ * uq) * (vq + α * (vp - κ * vq))
      = uq * (vp - κ * vq) + (α * (up - κ * uq)) * (vp - κ * vq)
        - ((up - κ * uq) * vq + (up - κ * uq) * (α * (vp - κ * vq))) := by
          rw [Int.add_mul, Int.mul_add]
    _ = uq * (vp - κ * vq) - (up - κ * uq) * vq := by
          have hCancel : (α * (up - κ * uq)) * (vp - κ * vq) = (up - κ * uq) * (α * (vp - κ * vq)) := by
            rw [Int.mul_assoc, Int.mul_left_comm]
          omega
    _ = uq * vp - up * vq := by
          rw [Int.mul_sub, Int.sub_mul, ← Int.mul_assoc uq κ vq, Int.mul_comm uq κ]
          omega

/-- Integrador simétrico Störmer-Verlet (Leapfrog) para cualquier ley de fuerza `F(q)` -/
def flipP (s : PhaseVec) : PhaseVec := ⟨s.q, -s.p⟩

def leapfrog (F : Int → Int) (s : PhaseVec) : PhaseVec :=
  let pHalf := s.p + F s.q
  let qNext := s.q + pHalf
  let pNext := pHalf + F qNext
  ⟨qNext, pNext⟩

theorem leapfrog_reversible (F : Int → Int) (s : PhaseVec) :
    flipP (leapfrog F (flipP (leapfrog F s))) = s := by
  cases s with | mk q p =>
  dsimp [leapfrog, flipP]
  have hQ : q + (p + F q) + (-(p + F q + F (q + (p + F q))) + F (q + (p + F q))) = q := by omega
  simp only [PhaseVec.mk.injEq]
  refine ⟨hQ, ?_⟩
  rw [hQ]; omega

#eval omegaForm (symplecticEuler 4 3 ⟨1, 0⟩) (symplecticEuler 4 3 ⟨0, 1⟩) -- 1 (exacto!)
```

---

## 3. De Liouville a Boltzmann: Balance Detallado y Equilibrio Térmico

Cuando un sistema hamiltoniano de muchos grados de libertad interactúa con un baño térmico a temperatura $T$, las probabilidades macroscópicas evolucionan hacia la distribución canónica de **Boltzmann-Gibbs** $w_i \propto e^{-\beta E_i}$ gobernada por el **Balance Detallado** ($w_1 t_{12} = w_2 t_{21}$), cuya estacionariedad exacta verificamos en [`LeanTT/M75_StatisticalMechanicsAndEntropy.lean`](../../LeanTT/M75_StatisticalMechanicsAndEntropy.lean).

---

👉 **Siguiente lección:** [**Lección 04 — Relatividad Especial, Espacio-Tiempo de Minkowski $\mathbb{R}^{1,3}$ y Transformaciones de Lorentz**](04_relatividad_especial_minkowski_y_lorentz.md)
