# Lección 01: Análisis Dimensional Dependiente y Seguridad Estática del Sistema Internacional (SI) en Lean 4

> **Módulos ejecutables asociados:** [`LeanTT/M71_DimensionalAnalysisAndSIUnits.lean`](../../LeanTT/M71_DimensionalAnalysisAndSIUnits.lean) y [`LeanTT/Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean`](../../LeanTT/Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean).
> **Navegación:** [⬅ Índice del Mini-Curso](00_indice_minicurso_fisica_lean4.md) | [Siguiente: Mecánica Lagrangiana y Noether ➡](02_mecanica_lagrangiana_accion_y_noether.md)

---

## 1. Por Qué los Tipos Dependientes Son el Lenguaje Natural de las Dimensiones Físicas

En lenguajes científicos convencionales (Python/NumPy, C++, Fortran), la masa `m = 5.0`, la longitud `x = 12.0` y el tiempo `t = 3.0` tienen exactamente el mismo tipo: `Float`. El compilador acepta sin rechistar aberraciones físicas como `m + t` o `Fuerza + Velocidad`.

En física matemática (Fourier 1822; Maxwell 1873; Buckingham 1914), las dimensiones fundamentales del Sistema Internacional $(L, M, T, I, \Theta, N, J)$ generan un **grupo abeliano libre de rango 7 isomorfo a $\mathbb{Z}^7$**:
* Multiplicar magnitudes **suma** los vectores de exponentes: $[x \cdot y] = [x] + [y] \in \mathbb{Z}^7$.
* Dividir magnitudes **resta** los vectores de exponentes: $[x / y] = [x] - [y] \in \mathbb{Z}^7$.
* Sumar o igualar magnitudes **exige igualdad estricta de índices**: $[x] = [y]$.

En Lean 4 codificamos esta disciplina como una **familia de tipos indexada por un valor** `Quantity : Dim → Type`:

```lean
namespace CursoFisica.L01

/-- Vector de exponentes dimensionales (Longitud L, Masa M, Tiempo T, Corriente I): -/
structure Dim where
  L : Int := 0
  M : Int := 0
  T : Int := 0
  I : Int := 0
  deriving Repr, DecidableEq

def Dim.one : Dim := {}
def Dim.mul (a b : Dim) : Dim := ⟨a.L + b.L, a.M + b.M, a.T + b.T, a.I + b.I⟩
def Dim.inv (a : Dim)   : Dim := ⟨-a.L, -a.M, -a.T, -a.I⟩
def Dim.div (a b : Dim) : Dim := Dim.mul a (Dim.inv b)

-- Catálogo de dimensiones del SI:
def Length       : Dim := { L := 1 }
def Mass         : Dim := { M := 1 }
def Time         : Dim := { T := 1 }
def Current      : Dim := { I := 1 }
def Velocity     : Dim := Dim.div Length Time        -- L¹ T⁻¹
def Acceleration : Dim := Dim.div Velocity Time      -- L¹ T⁻²
def Force        : Dim := Dim.mul Mass Acceleration  -- L¹ M¹ T⁻²
def Energy       : Dim := Dim.mul Force Length       -- L² M¹ T⁻²
def Action       : Dim := Dim.mul Energy Time        -- L² M¹ T⁻¹ (constante de Planck ħ)
def Charge       : Dim := Dim.mul Current Time       -- T¹ I¹
def Voltage      : Dim := Dim.div Energy Charge      -- L² M¹ T⁻³ I⁻¹

/-- Magnitud física indexada por su dimensión `d : Dim` -/
structure Quantity (d : Dim) where
  val : Int
  deriving Repr, DecidableEq

def qadd {d : Dim} (x y : Quantity d) : Quantity d := ⟨x.val + y.val⟩
def qsub {d : Dim} (x y : Quantity d) : Quantity d := ⟨x.val - y.val⟩
def qmul {d1 d2 : Dim} (x : Quantity d1) (y : Quantity d2) : Quantity (Dim.mul d1 d2) :=
  ⟨x.val * y.val⟩

-- Leyes de grupo abeliano verificadas automáticamente:
theorem dim_mul_comm (a b : Dim) : Dim.mul a b = Dim.mul b a := by
  cases a; cases b
  dsimp [Dim.mul]
  simp only [Dim.mk.injEq]
  exact ⟨by omega, by omega, by omega, by omega⟩

-- Unificación dimensional: Trabajo mecánico = Energía eléctrica (Carga × Voltaje) = Masa × Velocidad²
theorem unificacion_dimensional_energia :
    Dim.mul Charge Voltage = Energy ∧
    Dim.mul Mass (Dim.mul Velocity Velocity) = Energy ∧
    Dim.div Action Time = Energy := by
  decide

end CursoFisica.L01
```

---

## 2. Transporte Dimensional y el Teorema Trabajo-Energía

Observa un detalle sutil de la Teoría de Tipos Dependientes:
* Cuando calculamos `qmul m (qmul v v)` con `m : Quantity Mass` y `v : Quantity Velocity`, su tipo inferido es `Quantity (Dim.mul Mass (Dim.mul Velocity Velocity))`.
* Como `Mass`, `Velocity` y `Energy` son definiciones cerradas sobre enteros, el procedimiento de decisión `by decide` certifica automáticamente la igualdad de exponentes en tiempo de compilación, y el operador de transporte `▸` convierte el tipo a `Quantity Energy` sin coste en tiempo de ejecución!

Comprobémoslo en el Playground:

```lean
open CursoFisica.L01

/-- Segunda Ley de Newton tipada: F = m · a -/
def newtonForce (m : Quantity Mass) (a : Quantity Acceleration) : Quantity Force :=
  qmul m a

/-- Doble de la energía cinética: 2·Ek = m · v² : Quantity Energy (¡transporte certificado!) -/
def doubleKinetic (m : Quantity Mass) (v : Quantity Velocity) : Quantity Energy :=
  have hDim : Dim.mul Mass (Dim.mul Velocity Velocity) = Energy := by decide
  hDim ▸ qmul m (qmul v v)

#eval newtonForce ⟨10⟩ ⟨3⟩       -- { val := 30 } : Quantity Force (30 N)
#eval doubleKinetic ⟨10⟩ ⟨6⟩     -- { val := 360 } : Quantity Energy
```

---

## 3. Ejercicio Resuelto: Verificación Dimensional de la Ley de Planck-De Broglie

En mecánica cuántica, la constante de Planck $\hbar$ tiene dimensión de **Acción** ($[L^2 M^1 T^{-1}]$), y el momento lineal $p = \hbar k$ relaciona $\hbar$ con el número de onda $k$ de dimensión $L^{-1}$. Demostremos en Lean 4 que $\text{Action} \cdot L^{-1} = \text{Mass} \cdot \text{Velocity}$:

```lean
open CursoFisica.L01

def Wavenumber : Dim := Dim.inv Length
def Momentum   : Dim := Dim.mul Mass Velocity

theorem de_broglie_dimensional_check :
    Dim.mul Action Wavenumber = Momentum := by
  decide
```

---

👉 **Siguiente lección:** [**Lección 02 — Mecánica Lagrangiana, Principio de Mínima Acción y Teorema de Noether en Lean 4**](02_mecanica_lagrangiana_accion_y_noether.md)
