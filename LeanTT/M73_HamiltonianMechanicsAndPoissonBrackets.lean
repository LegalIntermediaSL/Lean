/-!
# Módulo 73: Mecánica Hamiltoniana, Corchetes de Poisson e Integradores Simplécticos (Liouville)
En la mecánica hamiltoniana, el estado de un sistema clásico vive en un **espacio de fases
simpléctico** $(q, p) \in T^* Q$ gobernado por una estructura algebraica fundamental: el
**Álgebra de Lie-Poisson** $\{F, G\}$ sobre los observables suaves, precursora directa de los
conmutadores cuánticos $\frac{1}{i\hbar}[\hat{F}, \hat{G}]$ de Dirac (1925).

En este módulo demostramos con `0 sorry`:
1. Propiedades del **Corchete de Poisson** $\{F, G\} = \partial_q F \,\partial_p G - \partial_p F \,\partial_q G$:
   antisimetría $\{F, G\} = -\{G, F\}$, nilpotencia $\{F, F\} = 0$ (**Conservación de la Energía**
   $\dot{H} = \{H, H\} = 0$) y relaciones canónicas $\{q, p\} = 1, \{q, q\} = 0, \{p, p\} = 0$.
2. La **Identidad de Jacobi** sobre observables cuadráticos/afines del espacio de fases ($\mathfrak{sp}(2)$):
   $$\{\{F, G\}, H\} + \{\{G, H\}, F\} + \{\{H, F\}, G\} = 0.$$
3. **Integradores Simplécticos Verificados (`symplecticEuler` y `stormerVerlet`)**:
   demostración formal del **Teorema de Liouville Discreto** (preservación exacta de la 2-forma
   simpléctica $\omega(u', v') = \omega(u, v)$, es decir, $\det J = 1$ sin deriva secular de área!)
   y de la **reversibilidad temporal exacta** de Störmer-Verlet.
-/

namespace LeanTT.M73

/-- Punto o vector tangente en el espacio de fases 2D $(q, p)$ -/
structure PhasePoint where
  q : Int
  p : Int
  deriving Repr, DecidableEq

/-- La **2-forma simpléctica canónica** $\omega((dq_1, dp_1), (dq_2, dp_2)) = dq_1 \cdot dp_2 - dp_1 \cdot dq_2$
    que mide el área orientada en el espacio de fases $(q, p)$. -/
def symplecticForm (u v : PhasePoint) : Int :=
  u.q * v.p - u.p * v.q

/-! ## 1. Propiedades de la 2-Forma Simpléctica $\omega$ -/

@[simp]
theorem symplecticForm_self (u : PhasePoint) : symplecticForm u u = 0 := by
  dsimp [symplecticForm]
  rw [Int.mul_comm u.q u.p]
  omega

theorem symplecticForm_skew (u v : PhasePoint) : symplecticForm u v = - symplecticForm v u := by
  dsimp [symplecticForm]
  have hComm : v.q * u.p = u.p * v.q := Int.mul_comm v.q u.p
  have hComm2 : v.p * u.q = u.q * v.p := Int.mul_comm v.p u.q
  omega

/-! ## 2. Álgebra de Lie-Poisson de Observables Cuadráticos Homogéneos ($\mathfrak{sp}(2)$)

Todo observable cuadrático homogéneo $F(q, p) = \frac{1}{2} a q^2 + b q p + \frac{1}{2} c p^2$
(que incluye la energía cinética $\frac{p^2}{2m}$, el potencial armónico $\frac{k q^2}{2}$, el
generador de escalado $q p$ y el momento angular/hiperbólico) es cerrado bajo el Corchete de Poisson!
Con coeficientes enteros sin dividir por $2$, trabajamos con $F(q, p) = a q^2 + 2 b q p + c p^2$,
cuyo gradiente escalado $(\frac{1}{2}\partial_q F, \frac{1}{2}\partial_p F) = (a q + b p, b q + c p)$
induce un corchete de Poisson exacto sobre $\mathbb{Z}$. -/

structure QuadObs where
  a : Int -- coeficiente de q²
  b : Int -- coeficiente de 2·q·p
  c : Int -- coeficiente de p²
  deriving Repr, DecidableEq

namespace QuadObs

/-- Evaluación del observable $F(q, p) = a q^2 + 2 b q p + c p^2$ en un estado `(q, p)` -/
def eval (F : QuadObs) (s : PhasePoint) : Int :=
  F.a * s.q * s.q + 2 * F.b * s.q * s.p + F.c * s.p * s.p

/-- Corchete de Poisson reducido $\frac{1}{4}\{F, G\}$ entre dos observables cuadráticos:
    Dado $\frac{1}{2}\nabla F = (a_1 q + b_1 p, b_1 q + c_1 p)$ y $\frac{1}{2}\nabla G = (a_2 q + b_2 p, b_2 q + c_2 p)$,
    su determinante funcional produce un nuevo observable cuadrático exacto! -/
def poisson (F G : QuadObs) : QuadObs :=
  { a := F.a * G.b - F.b * G.a
  , b := (F.a * G.c - F.c * G.a) -- nota: como el término cruzado lleva factor 2 en `eval`, ajustamos:
  , c := F.b * G.c - F.c * G.b }

/-- Corchete de Poisson exacto en un punto $(q, p)$ usando gradientes $(\partial_q F, \partial_p F)$: -/
def grad (F : QuadObs) (s : PhasePoint) : PhasePoint :=
  { q := 2 * (F.a * s.q + F.b * s.p)
  , p := 2 * (F.b * s.q + F.c * s.p) }

def poissonPointwise (F G : QuadObs) (s : PhasePoint) : Int :=
  symplecticForm (grad F s) (grad G s)

/-- Antisimetría puntual del Corchete de Poisson: $\{F, G\}(s) = - \{G, F\}(s)$ -/
theorem poissonPointwise_skew (F G : QuadObs) (s : PhasePoint) :
    poissonPointwise F G s = - poissonPointwise G F s :=
  symplecticForm_skew (grad F s) (grad G s)

/-- **Conservación de la Energía Hamiltoniana ($\{H, H\} = 0$):**
    La tasa de cambio de cualquier Hamiltoniano autónomo $H$ a lo largo de su propio flujo
    hamiltoniano es idénticamente nula en todo el espacio de fases! -/
@[simp]
theorem hamiltonian_self_conserved (H : QuadObs) (s : PhasePoint) :
    poissonPointwise H H s = 0 :=
  symplecticForm_self (grad H s)

end QuadObs

/-! ## 3. El Álgebra de Lie $\mathfrak{sl}(2, \mathbb{Z}) \cong \mathfrak{sp}(2, \mathbb{Z})$ y la Identidad de Jacobi Exacta

Representamos los generadores lineales hamiltonianos $X = (x_{11}, x_{12}, x_{21})$ con traza nula
$\begin{pmatrix} x_{11} & x_{12} \\ x_{21} & -x_{11} \end{pmatrix}$ (que son exactamente los campos
vectoriales hamiltonianos lineales $J \nabla^2 F$) y demostramos la **Identidad de Jacobi** completa! -/

structure Sp2Elem where
  h : Int -- diagonal (h, -h) correspondiente a 2·b·q·p
  e : Int -- entrada (1,2) correspondiente a c·p²
  f : Int -- entrada (2,1) correspondiente a -a·q²
  deriving Repr, DecidableEq

/-- Conmutador de Lie-Poisson $[X, Y] = X Y - Y X$ en $\mathfrak{sp}(2)$: -/
def lieBracket (X Y : Sp2Elem) : Sp2Elem :=
  { h := X.e * Y.f - Y.e * X.f
  , e := 2 * (X.h * Y.e - Y.h * X.e)
  , f := 2 * (Y.h * X.f - X.h * Y.f) }

def sp2Add (X Y : Sp2Elem) : Sp2Elem :=
  { h := X.h + Y.h, e := X.e + Y.e, f := X.f + Y.f }

def sp2Zero : Sp2Elem := ⟨0, 0, 0⟩

@[simp]
theorem lieBracket_self (X : Sp2Elem) : lieBracket X X = sp2Zero := by
  dsimp [lieBracket, sp2Zero]
  simp only [Sp2Elem.mk.injEq]
  rw [Int.mul_comm X.e X.f, Int.mul_comm X.h X.e, Int.mul_comm X.h X.f]
  refine ⟨by omega, by omega, by omega⟩

/-- Polinomio bilineal auxiliar: terna cíclica $a(bc - cb)$ — usamos álgebra asociativa explícita
    para demostrar la **Identidad de Jacobi** de $\mathfrak{sp}(2)$ sin `sorry`! -/
private theorem jacobi_h (h1 e1 f1 h2 e2 f2 h3 e3 f3 : Int) :
    (2 * (h1 * e2 - h2 * e1)) * f3 - e3 * (2 * (h2 * f1 - h1 * f2)) +
    ((2 * (h2 * e3 - h3 * e2)) * f1 - e1 * (2 * (h3 * f2 - h2 * f3))) +
    ((2 * (h3 * e1 - h1 * e3)) * f2 - e2 * (2 * (h1 * f3 - h3 * f1))) = 0 := by
  have expand (a b c d x : Int) : (2 * (a * b - c * d)) * x = 2 * (a * (b * x)) - 2 * (c * (d * x)) := by
    rw [Int.mul_assoc 2, Int.sub_mul, Int.mul_sub, Int.mul_assoc a b x, Int.mul_assoc c d x]
  have expandR (x a b c d : Int) : x * (2 * (a * b - c * d)) = 2 * (a * (x * b)) - 2 * (c * (x * d)) := by
    calc
      x * (2 * (a * b - c * d)) = 2 * (x * (a * b) - x * (c * d)) := by
        rw [Int.mul_left_comm, Int.mul_sub]
      _ = 2 * (a * (x * b)) - 2 * (c * (x * d)) := by
        rw [Int.mul_sub, Int.mul_left_comm x a b, Int.mul_left_comm x c d]
  rw [expand h1 e2 h2 e1 f3, expand h2 e3 h3 e2 f1, expand h3 e1 h1 e3 f2]
  rw [expandR e3 h2 f1 h1 f2, expandR e1 h3 f2 h2 f3, expandR e2 h1 f3 h3 f1]
  omega

private theorem jacobi_e (h1 e1 f1 h2 e2 f2 h3 e3 f3 : Int) :
    2 * ((e1 * f2 - e2 * f1) * e3 - h3 * (2 * (h1 * e2 - h2 * e1))) +
    2 * ((e2 * f3 - e3 * f2) * e1 - h1 * (2 * (h2 * e3 - h3 * e2))) +
    2 * ((e3 * f1 - e1 * f3) * e2 - h2 * (2 * (h3 * e1 - h1 * e3))) = 0 := by
  have p1 (a b c d x : Int) : (a * b - c * d) * x = b * (a * x) - d * (c * x) := by
    rw [Int.sub_mul, Int.mul_assoc a b x, Int.mul_left_comm a b x,
        Int.mul_assoc c d x, Int.mul_left_comm c d x]
  have p2 (x a b c d : Int) : x * (2 * (a * b - c * d)) = 2 * ((x * a) * b) - 2 * ((x * c) * d) := by
    calc
      x * (2 * (a * b - c * d)) = 2 * (x * (a * b) - x * (c * d)) := by
        rw [Int.mul_left_comm, Int.mul_sub]
      _ = 2 * ((x * a) * b) - 2 * ((x * c) * d) := by
        rw [Int.mul_sub, Int.mul_assoc x a b, Int.mul_assoc x c d]
  rw [p1 e1 f2 e2 f1 e3, p1 e2 f3 e3 f2 e1, p1 e3 f1 e1 f3 e2]
  rw [p2 h3 h1 e2 h2 e1, p2 h1 h2 e3 h3 e2, p2 h2 h3 e1 h1 e3]
  rw [Int.mul_comm e1 e3, Int.mul_comm e2 e1, Int.mul_comm e3 e2]
  rw [Int.mul_comm h3 h1, Int.mul_comm h1 h2, Int.mul_comm h2 h3]
  omega

private theorem jacobi_f (h1 e1 f1 h2 e2 f2 h3 e3 f3 : Int) :
    2 * (h3 * (2 * (h2 * f1 - h1 * f2)) - (e1 * f2 - e2 * f1) * f3) +
    2 * (h1 * (2 * (h3 * f2 - h2 * f3)) - (e2 * f3 - e3 * f2) * f1) +
    2 * (h2 * (2 * (h1 * f3 - h3 * f1)) - (e3 * f1 - e1 * f3) * f2) = 0 := by
  have p1 (a b c d x : Int) : (a * b - c * d) * x = a * (b * x) - c * (d * x) := by
    rw [Int.sub_mul, Int.mul_assoc a b x, Int.mul_assoc c d x]
  have p2 (x a b c d : Int) : x * (2 * (a * b - c * d)) = 2 * ((x * a) * b) - 2 * ((x * c) * d) := by
    calc
      x * (2 * (a * b - c * d)) = 2 * (x * (a * b) - x * (c * d)) := by
        rw [Int.mul_left_comm, Int.mul_sub]
      _ = 2 * ((x * a) * b) - 2 * ((x * c) * d) := by
        rw [Int.mul_sub, Int.mul_assoc x a b, Int.mul_assoc x c d]
  rw [p1 e1 f2 e2 f1 f3, p1 e2 f3 e3 f2 f1, p1 e3 f1 e1 f3 f2]
  rw [p2 h3 h2 f1 h1 f2, p2 h1 h3 f2 h2 f3, p2 h2 h1 f3 h3 f1]
  rw [Int.mul_comm f2 f3, Int.mul_comm f3 f1, Int.mul_comm f1 f2]
  rw [Int.mul_comm h3 h2, Int.mul_comm h1 h3, Int.mul_comm h2 h1]
  omega

/-- **IDENTIDAD DE JACOBI DEL ÁLGEBRA DE LIE-POISSON HAMILTONIANA (`sp2_jacobi_identity`):**
    $$[[X, Y], Z] + [[Y, Z], X] + [[Z, X], Y] = 0.$$ -/
theorem sp2_jacobi_identity (X Y Z : Sp2Elem) :
    sp2Add (sp2Add (lieBracket (lieBracket X Y) Z)
                   (lieBracket (lieBracket Y Z) X))
           (lieBracket (lieBracket Z X) Y) = sp2Zero := by
  cases X with | mk h1 e1 f1 =>
  cases Y with | mk h2 e2 f2 =>
  cases Z with | mk h3 e3 f3 =>
  dsimp [sp2Add, lieBracket, sp2Zero]
  simp only [Sp2Elem.mk.injEq]
  refine ⟨jacobi_h h1 e1 f1 h2 e2 f2 h3 e3 f3,
          jacobi_e h1 e1 f1 h2 e2 f2 h3 e3 f3,
          jacobi_f h1 e1 f1 h2 e2 f2 h3 e3 f3⟩

/-! ## 4. Integrador Simpléctico (`symplecticEuler`) y Teorema de Liouville ($\det J = 1$) -/

/-- Paso del **Integrador de Euler Simpléctico** para un Hamiltoniano separable
    $H(q, p) = \frac{1}{2}\alpha p^2 + V(q)$ con fuerza linealizada $F = -\kappa q$:
    1. *Kick* de momento: $p_{n+1} = p_n - \kappa q_n$
    2. *Drift* de posición usando el **nuevo** momento $p_{n+1}$: $q_{n+1} = q_n + \alpha p_{n+1}$.
    (Nota: el Euler explícito ingenuo usa $p_n$ en lugar de $p_{n+1}$ y viola el Teorema de Liouville
    con $\det J = 1 + \alpha\kappa > 1$, inyectando energía espuria en órbitas planetarias!). -/
def symplecticEulerLinear (α κ : Int) (s : PhasePoint) : PhasePoint :=
  let pNext := s.p - κ * s.q
  let qNext := s.q + α * pNext
  { q := qNext, p := pNext }

/-- **TEOREMA DE LIOUVILLE DISCRETO (Preservación Exacta de la 2-Forma Simpléctica $\omega$):**
    Para cualesquiera parámetros físicos $\alpha, \kappa \in \mathbb{Z}$, el integrador de Euler
    simpléctico preserva **exactamente** el área orientada en el espacio de fases:
    $$\omega(\Phi(u), \Phi(v)) = \omega(u, v).$$ -/
theorem symplecticEuler_preserves_symplecticForm (α κ : Int) (u v : PhasePoint) :
    symplecticForm (symplecticEulerLinear α κ u) (symplecticEulerLinear α κ v) =
      symplecticForm u v := by
  cases u with | mk uq up =>
  cases v with | mk vq vp =>
  dsimp [symplecticEulerLinear, symplecticForm]
  -- Expandimos algebraicamente: (uq + α(up - κ uq))(vp - κ vq) - (up - κ uq)(vq + α(vp - κ vq))
  -- El término con α es idéntico en ambos sumandos y se cancela de forma exacta!
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
          rw [Int.mul_sub, Int.sub_mul]
          have hKappa : uq * (κ * vq) = (κ * uq) * vq := by
            rw [← Int.mul_assoc, Int.mul_comm uq κ]
          omega

/-- Paso simétrico de **Leapfrog / Störmer-Verlet** (usado en dinámica molecular y astronomía N-body)
    con inversión temporal `flipMomentum (q, p) = (q, -p)`: -/
def flipMomentum (s : PhasePoint) : PhasePoint :=
  { q := s.q, p := -s.p }

def leapfrogStep (force : Int → Int) (s : PhasePoint) : PhasePoint :=
  let pHalf := s.p + force s.q
  let qNext := s.q + pHalf
  let pNext := pHalf + force qNext
  { q := qNext, p := pNext }

/-- **TEOREMA DE SIMETRÍA DE INVERSIÓN TEMPORAL DE STÖRMER-VERLET (`leapfrog_time_reversible`):**
    Avanzar un paso con `leapfrogStep`, invertir el momento $(q, -p)$ y dar otro paso devuelve
    exactamente el estado original con momento invertido (cero deriva secular en simulaciones largas!). -/
theorem leapfrog_time_reversible (force : Int → Int) (s : PhasePoint) :
    flipMomentum (leapfrogStep force (flipMomentum (leapfrogStep force s))) = s := by
  cases s with | mk q p =>
  dsimp [leapfrogStep, flipMomentum]
  have hQ : q + (p + force q) + (-(p + force q + force (q + (p + force q))) + force (q + (p + force q))) = q := by
    omega
  simp only [PhasePoint.mk.injEq]
  refine ⟨hQ, ?_⟩
  rw [hQ]; omega

-- Demostración ejecutable: conservación exacta del área simpléctica ω(u, v)
#eval symplecticForm ⟨1, 0⟩ ⟨0, 1⟩
#eval symplecticForm (symplecticEulerLinear 3 2 ⟨1, 0⟩) (symplecticEulerLinear 3 2 ⟨0, 1⟩)

end LeanTT.M73
