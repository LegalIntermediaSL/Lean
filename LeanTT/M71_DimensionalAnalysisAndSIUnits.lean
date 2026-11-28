/-!
# Módulo 71: Análisis Dimensional Dependiente y Sistema Internacional de Unidades (SI)
Inspirado en **PhysLean (HepLean)** y sistemas de tipos para computación física segura:
codificamos el grupo abeliano libre $\mathbb{Z}^7$ de las **7 dimensiones fundamentales del SI**
directamente en el índice del tipo dependiente `Quantity (d : Dim)`.

Gracias a los tipos dependientes de Lean 4:
1. Sumar metros con segundos (`Length + Time`) es un **error de tipos en tiempo de compilación**
   (evitando fallos catastróficos como el de la sonda *Mars Climate Orbiter* de 1999).
2. Multiplicar o dividir magnitudes calcula automáticamente la dimensión resultante en el tipo:
   $$\text{Fuerza} = \text{Masa} \cdot \text{Longitud} \cdot \text{Tiempo}^{-2} = [L^1 M^1 T^{-2}].$$
3. Demostramos las leyes de grupo abeliano del álgebra dimensional y los teoremas de homogeneidad
   energética (trabajo mecánico = energía cinética = energía potencial gravitatoria).
-/

namespace LeanTT.M71

/-- Exponente entero de las 7 dimensiones base del Sistema Internacional (SI):
    Longitud (`L`), Masa (`M`), Tiempo (`T`), Corriente eléctrica (`I`),
    Temperatura termodinámica (`Θ`), Cantidad de sustancia (`N`) e Intensidad luminosa (`J`). -/
structure Dim where
  L : Int := 0
  M : Int := 0
  T : Int := 0
  I : Int := 0
  Θ : Int := 0
  N : Int := 0
  J : Int := 0
  deriving Repr, DecidableEq

namespace Dim

/-- Dimensión escalar adimensional $[1] = L^0 M^0 T^0 I^0 \Theta^0 N^0 J^0$ -/
def dimensionless : Dim := {}

/-- Producto de dimensiones (suma componente a componente de exponentes en $\mathbb{Z}^7$) -/
def mul (d1 d2 : Dim) : Dim :=
  { L := d1.L + d2.L
  , M := d1.M + d2.M
  , T := d1.T + d2.T
  , I := d1.I + d2.I
  , Θ := d1.Θ + d2.Θ
  , N := d1.N + d2.N
  , J := d1.J + d2.J }

/-- Dimensión inversa $d^{-1}$ (negación de exponentes) -/
def inv (d : Dim) : Dim :=
  { L := -d.L, M := -d.M, T := -d.T, I := -d.I, Θ := -d.Θ, N := -d.N, J := -d.J }

/-- Cociente de dimensiones $d_1 / d_2 = d_1 \cdot d_2^{-1}$ -/
def div (d1 d2 : Dim) : Dim :=
  mul d1 (inv d2)

/-- Potencia entera $d^k$ de una dimensión física -/
def pow (d : Dim) (k : Int) : Dim :=
  { L := k * d.L, M := k * d.M, T := k * d.T, I := k * d.I, Θ := k * d.Θ, N := k * d.N, J := k * d.J }

-- Dimensiones fundamentales y derivadas clásicas/electromagnéticas del SI:
def Length       : Dim := { L := 1 }
def Mass         : Dim := { M := 1 }
def Time         : Dim := { T := 1 }
def Current      : Dim := { I := 1 }
def Velocity     : Dim := div Length Time                          -- L¹ T⁻¹
def Acceleration : Dim := div Velocity Time                        -- L¹ T⁻²
def Momentum     : Dim := mul Mass Velocity                        -- L¹ M¹ T⁻¹
def Force        : Dim := mul Mass Acceleration                    -- L¹ M¹ T⁻² (Newton)
def Energy       : Dim := mul Force Length                         -- L² M¹ T⁻² (Joule)
def Power        : Dim := div Energy Time                          -- L² M¹ T⁻³ (Watt)
def Action       : Dim := mul Energy Time                          -- L² M¹ T⁻¹ (Planck ħ)
def Charge       : Dim := mul Current Time                         -- T¹ I¹     (Coulomb)
def Voltage      : Dim := div Energy Charge                        -- L² M¹ T⁻³ I⁻¹ (Volt)

/-! ### Leyes de Grupo Abeliano del Álgebra de Dimensiones ($\mathbb{Z}^7$) -/

@[simp]
theorem mul_comm (d1 d2 : Dim) : mul d1 d2 = mul d2 d1 := by
  cases d1; cases d2
  simp [mul, Int.add_comm]

@[simp]
theorem mul_assoc (d1 d2 d3 : Dim) : mul (mul d1 d2) d3 = mul d1 (mul d2 d3) := by
  cases d1; cases d2; cases d3
  simp [mul, Int.add_assoc]

@[simp]
theorem mul_dimensionless (d : Dim) : mul d dimensionless = d := by
  cases d
  simp [mul, dimensionless]

@[simp]
theorem dimensionless_mul (d : Dim) : mul dimensionless d = d := by
  cases d
  simp [mul, dimensionless]

@[simp]
theorem mul_inv_cancel (d : Dim) : mul d (inv d) = dimensionless := by
  cases d
  dsimp [mul, inv, dimensionless]
  simp only [Dim.mk.injEq]
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

/-- Identidad dimensional fundamental de la Mecánica y el Electromagnetismo:
    $\text{Momentum} \cdot \text{Velocity} = \text{Force} \cdot \text{Length} = \text{Charge} \cdot \text{Voltage} = \text{Energy}$. -/
theorem energy_dimensional_unification :
    mul Momentum Velocity = Energy ∧ mul Charge Voltage = Energy ∧ mul Mass (pow Velocity 2) = Energy := by
  decide

end Dim

/-! ## Magnitudes Físicas Dependientemente Tipadas (`Quantity d`) -/

/-- Una magnitud física indexada estáticamente por su vector dimensional `d : Dim`.
    Usamos aritmética entera exacta (p. ej. unidades escaladas o enteras) para ejecución en el kernel. -/
structure Quantity (d : Dim) where
  val : Int
  deriving Repr, DecidableEq

namespace Quantity

/-- Suma homogénea: solo compila cuando ambos operandos comparten exactamente la dimensión `d`! -/
def add {d : Dim} (x y : Quantity d) : Quantity d :=
  ⟨x.val + y.val⟩

/-- Resta homogénea -/
def sub {d : Dim} (x y : Quantity d) : Quantity d :=
  ⟨x.val - y.val⟩

/--Escalado por un coeficiente adimensional entero -/
def smul {d : Dim} (c : Int) (x : Quantity d) : Quantity d :=
  ⟨c * x.val⟩

/-- Producto heterogéneo dependiente: multiplica valores y suma dimensiones en el tipo! -/
def qmul {d1 d2 : Dim} (x : Quantity d1) (y : Quantity d2) : Quantity (Dim.mul d1 d2) :=
  ⟨x.val * y.val⟩

/-- Segunda Ley de Newton tipada: $F = m \cdot a : \text{Quantity Force}$ -/
def newtonForce (m : Quantity Dim.Mass) (a : Quantity Dim.Acceleration) : Quantity Dim.Force :=
  qmul m a

/-- Trabajo mecánico tipado: $W = F \cdot \Delta x : \text{Quantity Energy}$ -/
def mechanicalWork (f : Quantity Dim.Force) (dx : Quantity Dim.Length) : Quantity Dim.Energy :=
  qmul f dx

/-- Doble de la energía cinética ($2 E_k = m v^2$) con transporte certificado de dimensión a `Energy`: -/
def doubleKineticEnergy (m : Quantity Dim.Mass) (v : Quantity Dim.Velocity) : Quantity Dim.Energy :=
  have hDim : Dim.mul Dim.Mass (Dim.mul Dim.Velocity Dim.Velocity) = Dim.Energy := by decide
  hDim ▸ qmul m (qmul v v)

/-- Acción clásica discreta en un intervalo temporal $\Delta t$: $\Delta S = L \cdot \Delta t : \text{Quantity Action}$ -/
def actionStep (lagrangian : Quantity Dim.Energy) (dt : Quantity Dim.Time) : Quantity Dim.Action :=
  qmul lagrangian dt

/-! ### Teoremas Verificados sobre Magnitudes Físicas Tipadas -/

theorem add_comm_quantity {d : Dim} (x y : Quantity d) : add x y = add y x := by
  cases x; cases y
  simp [add, Int.add_comm]

theorem smul_distrib_add {d : Dim} (c : Int) (x y : Quantity d) :
    smul c (add x y) = add (smul c x) (smul c y) := by
  cases x; cases y
  simp [smul, add, Int.mul_add]

/-- TEOREMA DE TRABAJO-ENERGÍA BAJO ACELERACIÓN UNIFORME (Galileo-Newton):
    Si una masa `m` parte de velocidad `v0` y acelera con `a` durante un tiempo `t`
    ($v_f = v_0 + a\cdot t$ y desplazamiento duplicado $2\Delta x = 2 v_0 t + a t^2$),
    entonces el doble del trabajo mecánico $F \cdot (2\Delta x)$ coincide exactamente con la
    variación de `doubleKineticEnergy`: $m v_f^2 - m v_0^2$! -/
theorem work_energy_uniform_accel (m v0 a t : Int) :
    let vf := v0 + a * t
    let twoDx := 2 * v0 * t + a * t * t
    let W2 := mechanicalWork (newtonForce ⟨m⟩ ⟨a⟩) ⟨twoDx⟩
    let Ekf := doubleKineticEnergy ⟨m⟩ ⟨vf⟩
    let Ek0 := doubleKineticEnergy ⟨m⟩ ⟨v0⟩
    W2 = sub Ekf Ek0 := by
  dsimp [mechanicalWork, newtonForce, doubleKineticEnergy, qmul, sub, Dim.Energy]
  simp only [Quantity.mk.injEq]
  have hPoly : (v0 + a * t) * (v0 + a * t) = v0 * v0 + a * (2 * v0 * t + a * t * t) := by
    have h1 : v0 * (a * t) + a * t * v0 = a * (2 * v0 * t) := by
      rw [Int.mul_left_comm v0 a t, Int.mul_assoc a t v0, Int.mul_comm t v0,
          Int.mul_assoc 2 v0 t, Int.two_mul, Int.mul_add]
    have h2 : a * t * (a * t) = a * (a * t * t) := by
      rw [← Int.mul_assoc (a * t) a t, Int.mul_comm (a * t) a, Int.mul_assoc a (a * t) t]
    calc
      (v0 + a * t) * (v0 + a * t)
        = v0 * v0 + (v0 * (a * t) + a * t * v0) + a * t * (a * t) := by
            simp only [Int.add_mul, Int.mul_add]; omega
      _ = v0 * v0 + a * (2 * v0 * t) + a * (a * t * t) := by rw [h1, h2]
      _ = v0 * v0 + a * (2 * v0 * t + a * t * t) := by rw [Int.mul_add, Int.add_assoc]
  rw [hPoly, Int.mul_add m (v0 * v0), ← Int.mul_assoc m a]
  omega

end Quantity

-- Demostración computacional ejecutable: m = 3 kg, v0 = 4 m/s, a = 2 m/s², t = 5 s
-- vf = 14 m/s, 2·Ek(vf) = 3 * 196 = 588 J, 2·Ek(v0) = 3 * 16 = 48 J => Δ(2·Ek) = 540 J
#eval Quantity.doubleKineticEnergy ⟨3⟩ ⟨14⟩
#eval Quantity.mechanicalWork (Quantity.newtonForce ⟨3⟩ ⟨2⟩) ⟨2 * 4 * 5 + 2 * 5 * 5⟩

end LeanTT.M71
