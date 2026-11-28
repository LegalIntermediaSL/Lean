/-!
# Módulo 74: Relatividad Especial, Espacio-Tiempo de Minkowski $\mathbb{R}^{1,3}$ y Grupo de Lorentz
Inspirado en **PhysLean (`HepLean` — módulo Lorentz / MinkowskiMatrix)**:
En 1905 Albert Einstein unificó espacio y tiempo, y en 1908 Hermann Minkowski reveló su estructura
geométrica profunda: un espacio vectorial tetradimensional equipado con el tensor métrico indefinido
de signatura $(+, -, -, -)$:
$$\eta(u, v) = c^2 u_t v_t - u_x v_x - u_y v_y - u_z v_z.$$

En este módulo formalizamos y demostramos con `0 sorry`:
1. Cuadrivectores `FourVec`, métrica de Minkowski $\eta$, simetría bilineal y clasificación causal
   invariante (`Timelike`, `Lightlike` / Cono de Luz, `Spacelike`).
2. **Transformaciones de Lorentz (*Boosts*) Parametrizadas Exactas** (ternas hiperbólicas de Minkowski
   con $\gamma^2 - \beta^2 \gamma^2 = s^2$, evitando toda aproximación de coma flotante):
   - **Teorema de Invariancia del Intervalo Espacio-Temporal** ($\eta(\Lambda u, \Lambda v) = s^2 \eta(u, v)$).
   - **Preservación Exacta del Cono de Luz** (constancia de la velocidad de la luz $c$ en todos los
     sistemas de referencia inerciales!).
3. **Ley de Adición Relativista de Velocidades de Einstein** ($u \oplus_c v = \frac{u + v}{1 + uv/c^2}$)
   y demostración formal de la **Barrera Sublumínica**: si $|u| < c$ y $|v| < c$, entonces $|u \oplus_c v| < c$!
4. **Relación de Dispersión Energía-Momento** $E^2 - (pc)^2 = (m_0 c^2)^2$ como invariante de Lorentz.
-/

namespace LeanTT.M74

/-- Cuadrivector contravariante $u^\mu = (t, x, y, z)$ en unidades naturales ($c = 1$) -/
structure FourVec where
  t : Int
  x : Int
  y : Int
  z : Int
  deriving Repr, DecidableEq

namespace FourVec

/-- Producto interno pseudoeuclídeo de Minkowski con signatura mayormente negativa $(+, -, -, -)$: -/
def minkowskiDot (u v : FourVec) : Int :=
  u.t * v.t - u.x * v.x - u.y * v.y - u.z * v.z

/-- Intervalo espacio-temporal cuadrático $ds^2 = \eta(u, u) = t^2 - x^2 - y^2 - z^2$: -/
def intervalSq (u : FourVec) : Int :=
  minkowskiDot u u

/-- Clasificación causal relativista del cuadrivector `u`: -/
def IsTimelike  (u : FourVec) : Prop := 0 < intervalSq u
def IsLightlike (u : FourVec) : Prop := intervalSq u = 0
def IsSpacelike (u : FourVec) : Prop := intervalSq u < 0

/-- Simetría del tensor métrico de Minkowski $\eta_{\mu\nu} = \eta_{\nu\mu}$: -/
theorem minkowskiDot_symm (u v : FourVec) : minkowskiDot u v = minkowskiDot v u := by
  dsimp [minkowskiDot]
  rw [Int.mul_comm u.t v.t, Int.mul_comm u.x v.x, Int.mul_comm u.y v.y, Int.mul_comm u.z v.z]

end FourVec

/-! ## 1. Transformaciones de Lorentz Exactas (Boosts Hiperbólicos Escalados)

Para trabajar con aritmética exacta en el kernel sin raíces cuadradas irracionales, representamos un
*boost* de Lorentz a lo largo del eje $X$ mediante una terna entera $(\gamma_s, \pi_s, s)$ que cumple
la identidad hiperbólica fundamental escalada ($\cosh^2 \phi - \sinh^2 \phi = 1$):
$$\gamma_s^2 - \pi_s^2 = s^2 \quad (s \neq 0),$$
donde la velocidad relativa es $v/c = \pi_s / \gamma_s$.
Por ejemplo, para $v = \frac{3}{5}c$, tomamos $(\gamma_s, \pi_s, s) = (5, 3, 4)$ pues $5^2 - 3^2 = 4^2$! -/

structure ScaledBoostX where
  gs : Int -- γ · s
  ps : Int -- β · γ · s
  s  : Int -- factor de escala no nulo (p. ej. 4 para v = 3/5 c)
  hyp_id : gs * gs - ps * ps = s * s

/-- Acción del *boost* de Lorentz escalado sobre cualquier cuadrivector $u = (t, x, y, z)$:
    $(s \cdot t', s \cdot x', s \cdot y', s \cdot z') = (\gamma_s t - \pi_s x,\; -\pi_s t + \gamma_s x,\; s y,\; s z)$. -/
def applyBoostX (B : ScaledBoostX) (u : FourVec) : FourVec :=
  { t := B.gs * u.t - B.ps * u.x
  , x := -(B.ps * u.t) + B.gs * u.x
  , y := B.s * u.y
  , z := B.s * u.z }

/-- Identidad algebraica de Brahmagupta-Minkowski para la parte $(t, x)$ en 1+1 dimensiones: -/
private theorem minkowski_1d_boost_id (gs ps ut ux vt vx : Int) :
    (gs * ut - ps * ux) * (gs * vt - ps * vx) - (-(ps * ut) + gs * ux) * (-(ps * vt) + gs * vx) =
      (gs * gs - ps * ps) * (ut * vt - ux * vx) := by
  calc
    (gs * ut - ps * ux) * (gs * vt - ps * vx) - (-(ps * ut) + gs * ux) * (-(ps * vt) + gs * vx)
      = (gs * gs) * (ut * vt) - (gs * ps) * (ut * vx) - (ps * gs) * (ux * vt) + (ps * ps) * (ux * vx)
        - ((ps * ps) * (ut * vt) - (ps * gs) * (ut * vx) - (gs * ps) * (ux * vt) + (gs * gs) * (ux * vx)) := by
          have hA : (gs * ut - ps * ux) * (gs * vt - ps * vx) =
              (gs * gs) * (ut * vt) - (gs * ps) * (ut * vx) - (ps * gs) * (ux * vt) + (ps * ps) * (ux * vx) := by
            simp only [Int.sub_mul, Int.mul_sub]
            have m1 : gs * ut * (gs * vt) = (gs * gs) * (ut * vt) := by
              rw [Int.mul_assoc, Int.mul_left_comm ut gs vt, ← Int.mul_assoc]
            have m2 : gs * ut * (ps * vx) = (gs * ps) * (ut * vx) := by
              rw [Int.mul_assoc, Int.mul_left_comm ut ps vx, ← Int.mul_assoc]
            have m3 : ps * ux * (gs * vt) = (ps * gs) * (ux * vt) := by
              rw [Int.mul_assoc, Int.mul_left_comm ux gs vt, ← Int.mul_assoc]
            have m4 : ps * ux * (ps * vx) = (ps * ps) * (ux * vx) := by
              rw [Int.mul_assoc, Int.mul_left_comm ux ps vx, ← Int.mul_assoc]
            rw [m1, m2, m3, m4]
            omega
          have hB : (-(ps * ut) + gs * ux) * (-(ps * vt) + gs * vx) =
              (ps * ps) * (ut * vt) - (ps * gs) * (ut * vx) - (gs * ps) * (ux * vt) + (gs * gs) * (ux * vx) := by
            have eqNeg : (-(ps * ut) + gs * ux) * (-(ps * vt) + gs * vx) =
                (gs * ux - ps * ut) * (gs * vx - ps * vt) := by
              congr 1 <;> omega
            rw [eqNeg]
            simp only [Int.sub_mul, Int.mul_sub]
            have n1 : gs * ux * (gs * vx) = (gs * gs) * (ux * vx) := by
              rw [Int.mul_assoc, Int.mul_left_comm ux gs vx, ← Int.mul_assoc]
            have n2 : gs * ux * (ps * vt) = (gs * ps) * (ux * vt) := by
              rw [Int.mul_assoc, Int.mul_left_comm ux ps vt, ← Int.mul_assoc]
            have n3 : ps * ut * (gs * vx) = (ps * gs) * (ut * vx) := by
              rw [Int.mul_assoc, Int.mul_left_comm ut gs vx, ← Int.mul_assoc]
            have n4 : ps * ut * (ps * vt) = (ps * ps) * (ut * vt) := by
              rw [Int.mul_assoc, Int.mul_left_comm ut ps vt, ← Int.mul_assoc]
            rw [n1, n2, n3, n4]
            omega
          rw [hA, hB]
    _ = (gs * gs - ps * ps) * (ut * vt - ux * vx) := by
          rw [Int.mul_comm gs ps]
          simp only [Int.sub_mul, Int.mul_sub]
          omega

/-- **TEOREMA DE INVARIANCIA DE MINKOWSKI BAJO EL GRUPO DE LORENTZ (`boostX_preserves_minkowskiDot`):**
    Todo *boost* de Lorentz preserva exactamente el producto escalar espacio-temporal de Minkowski
    (salvo el factor global de homogeneidad $s^2$):
    $$\eta(\Lambda u, \Lambda v) = s^2 \cdot \eta(u, v).$$ -/
theorem boostX_preserves_minkowskiDot (B : ScaledBoostX) (u v : FourVec) :
    FourVec.minkowskiDot (applyBoostX B u) (applyBoostX B v) =
      (B.s * B.s) * FourVec.minkowskiDot u v := by
  dsimp [FourVec.minkowskiDot, applyBoostX]
  have h1d := minkowski_1d_boost_id B.gs B.ps u.t u.x v.t v.x
  rw [B.hyp_id] at h1d
  have hy : B.s * u.y * (B.s * v.y) = (B.s * B.s) * (u.y * v.y) := by
    rw [Int.mul_assoc, Int.mul_left_comm u.y B.s v.y, ← Int.mul_assoc]
  have hz : B.s * u.z * (B.s * v.z) = (B.s * B.s) * (u.z * v.z) := by
    rw [Int.mul_assoc, Int.mul_left_comm u.z B.s v.z, ← Int.mul_assoc]
  -- Agrupamos los dos primeros términos para aplicar `h1d`:
  have hSplit :
      (B.gs * u.t - B.ps * u.x) * (B.gs * v.t - B.ps * v.x) -
      (-(B.ps * u.t) + B.gs * u.x) * (-(B.ps * v.t) + B.gs * v.x) -
      B.s * u.y * (B.s * v.y) - B.s * u.z * (B.s * v.z) =
      (B.s * B.s) * (u.t * v.t - u.x * v.x) - (B.s * B.s) * (u.y * v.y) - (B.s * B.s) * (u.z * v.z) := by
    rw [h1d, hy, hz]
  rw [hSplit]
  simp only [Int.mul_sub]

/-- Corolario inmediato: **Invariancia del Intervalo Espacio-Temporal** $ds'^2 = s^2 ds^2$ -/
theorem boostX_preserves_intervalSq (B : ScaledBoostX) (u : FourVec) :
    FourVec.intervalSq (applyBoostX B u) = (B.s * B.s) * FourVec.intervalSq u :=
  boostX_preserves_minkowskiDot B u u

/-- **POSTULADO DE INVARIANCIA DEL CONO DE LUZ (Constancia de $c$):**
    Si un rayo de luz viaja sobre el cono nulo (`IsLightlike u`, es decir, $t^2 = x^2 + y^2 + z^2$),
    entonces en cualquier otro sistema de referencia inercial sigue viajando exactamente sobre el
    cono de luz (`IsLightlike (applyBoostX B u)`)! -/
theorem boostX_preserves_lightcone (B : ScaledBoostX) {u : FourVec}
    (hLight : FourVec.IsLightlike u) :
    FourVec.IsLightlike (applyBoostX B u) := by
  dsimp [FourVec.IsLightlike] at *
  rw [boostX_preserves_intervalSq, hLight, Int.mul_zero]

/-- **RELACIÓN DE DISPERSIÓN ENERGÍA-MOMENTO DE EINSTEIN ($E^2 - p^2 = m_0^2$ en unidades $c=1$):**
    Para una partícula en reposo de masa $m_0$, su cuadrivector momento es $P_{\text{rest}} = (m_0, 0, 0, 0)$.
    Al aplicar cualquier *boost* de Lorentz, el cuadrimomento resultante $P' = (E', p'_x, 0, 0)$
    satisface idénticamente $E'^2 - p'^2_x = (s \cdot m_0)^2$! -/
theorem einstein_energy_momentum_invariant (B : ScaledBoostX) (m0 : Int) :
    let pBoosted := applyBoostX B ⟨m0, 0, 0, 0⟩
    pBoosted.t * pBoosted.t - pBoosted.x * pBoosted.x = (B.s * m0) * (B.s * m0) := by
  have h := boostX_preserves_intervalSq B ⟨m0, 0, 0, 0⟩
  dsimp [FourVec.intervalSq, FourVec.minkowskiDot, applyBoostX] at *
  simp only [Int.mul_zero, Int.sub_zero, Int.add_zero] at *
  have hSwap : (B.s * B.s) * (m0 * m0) = (B.s * m0) * (B.s * m0) := by
    rw [Int.mul_assoc B.s B.s (m0 * m0), ← Int.mul_assoc B.s m0 m0,
        Int.mul_comm B.s m0, Int.mul_assoc m0 B.s m0, ← Int.mul_assoc B.s m0 (B.s * m0)]
    rw [Int.mul_comm B.s m0]
  rw [hSwap] at h
  exact h

/-! ## 2. Barrera Sublumínica en la Adición Relativista de Velocidades ($u \oplus_c v = \frac{u + v}{1 + uv/c^2}$) -/

/-- **TEOREMA DE LA BARRERA DE LA VELOCIDAD DE LA LUZ (`subluminal_velocity_addition`):**
    En la ley de composición relativista $w = \frac{c^2(u + v)}{c^2 + u v}$, la diferencia entre el
    denominador y el numerador satisface la factorización exacta:
    $$(c^2 + u v) - c(u + v) = (c - u)(c - v) > 0,$$
    y la suma satisface:
    $$(c^2 + u v) + c(u + v) = (c + u)(c + v) > 0.$$
    Por tanto, si $|u| < c$ y $|v| < c$ (ambas partículas son sublumínicas), su velocidad relativa
    compuesta **nunca alcanza ni supera la velocidad de la luz $c$**:
    $$|c(u + v)| < c^2 + u v \quad \text{(equivalentemente } \left|\frac{u+v}{1 + uv/c^2}\right| < c\text{)}!$$ -/
theorem subluminal_velocity_addition {c u v : Int}
    (hu_lo : -c < u) (hu_hi : u < c)
    (hv_lo : -c < v) (hv_hi : v < c) :
    -(c * c + u * v) < c * (u + v) ∧ c * (u + v) < c * c + u * v := by
  have hPosUpper : 0 < (c - u) * (c - v) := Int.mul_pos (by omega) (by omega)
  have hPosLower : 0 < (c + u) * (c + v) := Int.mul_pos (by omega) (by omega)
  have hFactUpper : (c - u) * (c - v) = (c * c + u * v) - c * (u + v) := by
    simp only [Int.sub_mul, Int.mul_sub, Int.mul_add]
    rw [Int.mul_comm u c]
    omega
  have hFactLower : (c + u) * (c + v) = (c * c + u * v) + c * (u + v) := by
    simp only [Int.add_mul, Int.mul_add]
    rw [Int.mul_comm u c]
    omega
  omega

-- Ejemplo ejecutable: Boost de Lorentz con v = 3/5 c => (γs=5, πs=3, s=4, pues 5² - 3² = 4²)
def boost3Fifths : ScaledBoostX := ⟨5, 3, 4, by decide⟩

#eval applyBoostX boost3Fifths ⟨10, 0, 0, 0⟩ -- Dilatación temporal y momento relativista
#eval FourVec.intervalSq (applyBoostX boost3Fifths ⟨1, 1, 0, 0⟩) -- 0 (el fotón sigue en el cono de luz!)

end LeanTT.M74
