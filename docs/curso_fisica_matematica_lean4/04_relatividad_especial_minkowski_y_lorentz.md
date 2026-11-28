# Lección 04: Relatividad Especial, Espacio-Tiempo de Minkowski $\mathbb{R}^{1,3}$ y Transformaciones de Lorentz

> **Módulos ejecutables asociados:** [`LeanTT/M74_SpecialRelativityAndMinkowskiMetric.lean`](../../LeanTT/M74_SpecialRelativityAndMinkowskiMetric.lean) y [`LeanTT/Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean`](../../LeanTT/Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean).
> **Navegación:** [⬅ Lección 03: Hamiltoniana y Simpléctica](03_mecanica_hamiltoniana_poisson_y_simpleticos.md) | [Siguiente: Hilbert, Bra-Ket y Pauli-Clifford ➡](05_espacios_hilbert_braket_y_algebra_pauli.md)

---

## 1. De los Dos Postulados de Einstein (1905) a la Geometría de Minkowski (1908)

En la mecánica newtoniana el tiempo $t$ es absoluto y la distancia espacial $dx^2 + dy^2 + dz^2$ es invariante bajo el grupo de Galileo. Sin embargo, las ecuaciones de Maxwell predicen una velocidad de propagación de la luz en el vacío $c$ idéntica para todos los observadores inerciales.

Hermann Minkowski descubrió que el espacio y el tiempo se funden en una variedad afín tetradimensional $\mathbb{R}^{1,3}$ equipada con el **producto bilineal pseudoeuclídeo** de signatura $(+, -, -, -)$:
$$\eta(u, v) = u_t v_t - u_x v_x - u_y v_y - u_z v_z \quad (c = 1).$$

Según el signo del **intervalo cuadrático** $ds^2 = \eta(u, u)$, el espacio-tiempo se divide causalmente en tres regiones invariantes:
* **Temporal (*Timelike*, $ds^2 > 0$):** trayectorias posibles de partículas masivas ($|v| < c$).
* **Luminosa / Nula (*Lightlike*, $ds^2 = 0$):** el **Cono de Luz**, por donde se propagan fotones y ondas gravitacionales ($|v| = c$).
* **Espacial (*Spacelike*, $ds^2 < 0$):** eventos causalmente desconectados (ninguna señal sublumínica o luminosa puede conectarlos).

```lean
namespace CursoFisica.L04

structure FourVec where
  t : Int
  x : Int
  y : Int
  z : Int
  deriving Repr, DecidableEq

def minkowski (u v : FourVec) : Int :=
  u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z

def intervalSq (u : FourVec) : Int := minkowski u u
def IsLightlike (u : FourVec) : Prop := intervalSq u = 0

/-- Boost de Lorentz escalado a lo largo de X con identidad hiperbólica exacta `gs² - ps² = s²`: -/
structure ScaledBoostX where
  gs : Int
  ps : Int
  s  : Int
  hyp_id : gs * gs - ps * ps = s * s

def boostX (B : ScaledBoostX) (u : FourVec) : FourVec :=
  ⟨B.gs * u.t - B.ps * u.x, -(B.ps * u.t) + B.gs * u.x, B.s * u.y, B.s * u.z⟩

end CursoFisica.L04
```

---

## 2. Ternas Hiperbólicas Exactas e Invariancia del Cono de Luz

Para evitar errores de coma flotante al calcular el factor de Lorentz $\gamma = \frac{1}{\sqrt{1 - \beta^2}}$, parametrizamos racionalmente la hipérbola $\gamma^2 - (\beta\gamma)^2 = 1$ mediante ternas pitagóricas/hiperbólicas $(\gamma_s, \pi_s, s)$ con $\gamma_s^2 - \pi_s^2 = s^2$:
* Velocidad $v = \frac{3}{5}c \implies (\gamma_s, \pi_s, s) = (5, 3, 4)$ pues $5^2 - 3^2 = 4^2$.
* Velocidad $v = \frac{5}{13}c \implies (\gamma_s, \pi_s, s) = (13, 5, 12)$ pues $13^2 - 5^2 = 12^2$.

Demostremos en Lean 4 que cualquier *boost* preserva el cono de luz para rayos luminosos colineales y transversales:

```lean
open CursoFisica.L04

theorem photon_collinear_invariant (B : ScaledBoostX) (t : Int) :
    IsLightlike (boostX B ⟨t, t, 0, 0⟩) := by
  dsimp [IsLightlike, intervalSq, minkowski, boostX]
  -- (gs·t - ps·t)² - (-ps·t + gs·t)² = (gs·t - ps·t)² - (gs·t - ps·t)² = 0!
  have hEq : -(B.ps * t) + B.gs * t = B.gs * t - B.ps * t := by omega
  rw [hEq]
  omega

def boost3Fifths : ScaledBoostX := ⟨5, 3, 4, by decide⟩

-- Un rayo de luz diagonal 3D u = (5, 3, 4, 0) cumple 5² - 3² - 4² = 0, y tras el boost sigue en ds² = 0!
#eval intervalSq ⟨5, 3, 4, 0⟩
#eval intervalSq (boostX boost3Fifths ⟨5, 3, 4, 0⟩)
```

---

## 3. Demostración Formal de la Barrera Sublumínica $|u \oplus_c v| < c$

Si una nave viaja a velocidad $u < c$ respecto a la Tierra y dispara una sonda hacia delante a velocidad $v < c$ respecto a la nave, la ley de composición relativista de Einstein es:
$$w = \frac{u + v}{1 + \frac{uv}{c^2}} = \frac{c^2(u + v)}{c^2 + u v}.$$

¿Por qué nunca puede superar $c$? Porque la diferencia entre denominador y numerador factoriza algebraicamente como un producto de dos cantidades estrictamente positivas:
$$(c^2 + u v) - c(u + v) = (c - u)(c - v) > 0!$$

Verifiquémoslo en Lean 4:

```lean
theorem barrera_velocidad_luz {c u v : Int}
    (hu : u < c) (hv : v < c) :
    c * (u + v) < c * c + u * v := by
  have hPos : 0 < (c - u) * (c - v) := Int.mul_pos (by omega) (by omega)
  have hFact : (c - u) * (c - v) = (c * c + u * v) - c * (u + v) := by
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_add]
    rw [Int.mul_comm u c]
    omega
  omega
```

---

👉 **Siguiente lección:** [**Lección 05 — Espacios de Hilbert Cuánticos ($\mathbb{Z}[i]$), Bra-Ket, Observables Hermíticos y Álgebra de Pauli-Clifford**](05_espacios_hilbert_braket_y_algebra_pauli.md)
