/-!
# Módulo 61: Teoría de Tipos Cuantitativa (QTT estilo Idris 2) y Semianillo de Multiplicidades $\{0, 1, \omega\}$
## Ámbito: Sistemas de Tipos Subestructurales Dependientes, Borrado de Tipos ($0$) y Tipos Lineales ($1$)

En **Quantitative Type Theory (QTT)** de Bob Atkey (2018) y Conor McBride (2016) —el núcleo teórico
del lenguaje **Idris 2**—, cada variable del contexto $x :_\pi A$ lleva anotada una **multiplicidad**
$\pi \in \{0, 1, \omega\}$ que contabiliza cuántas veces se usa $x$ en tiempo de ejecución:
- **`0` (`zero`):** La variable se usa **0 veces en tiempo de ejecución** (solo puede aparecer dentro
  de tipos o pruebas que el compilador borrará garantizadamente — *Static Type Erasure*).
- **`1` (`one`):** La variable debe usarse **exactamente 1 vez** en tiempo de ejecución (recurso lineal:
  descriptores de fichero, punteros únicos, canales de protocolos de sesión).
- **`ω` (`many`):** La variable puede usarse un número arbitrario de veces ($0, 1, 2, \dots$).

En este módulo:
1. Formalizamos el tipo de multiplicidades `Mult` (`zero`, `one`, `many`) con su suma `addM` ($\pi + \rho$)
   y producto `mulM` ($\pi \cdot \rho$).
2. Demostramos que `(Mult, addM, mulM, zero, one)` forma un **Semianillo Conmutativo con Cero Absorbente**.
3. Formalizamos contextos de uso de variables `UsageVec` y demostramos el **Teorema de Borrado Estático (`scale_zero_erases_all`)**:
   al entrar en una posición de tipo (multiplicidad $0$), el consumo en tiempo de ejecución de todas
   las variables empleadas dentro del tipo colapsa exactamente a $0$.
-/

namespace LeanTT.M61

/-- Multiplicidades de recursos en Quantitative Type Theory (QTT): `{0, 1, ω}` -/
inductive Mult where
  | zero : Mult -- `0`: Borrado en tiempo de ejecución (solo tiempo de compilación / tipos)
  | one  : Mult -- `1`: Lineal (exactamente un uso en tiempo de ejecución)
  | many : Mult -- `ω`: Irrestricto (cualquier número de usos)
  deriving Repr, DecidableEq

namespace Mult

/-- Suma de multiplicidades (`π + ρ`):
    - `0 + ρ = ρ`
    - `1 + 1 = ω` (usar una variable lineal dos veces pasa a requerir multiplicidad `ω`) -/
@[simp]
def addM : Mult → Mult → Mult
  | .zero, m     => m
  | m,     .zero => m
  | _,     _     => .many

/-- Producto (escalado) de multiplicidades (`π · ρ`):
    Si construimos un término que se usará `π` veces y dentro usa `x` con multiplicidad `ρ`,
    el uso total de `x` es `π · ρ`. -/
@[simp]
def mulM : Mult → Mult → Mult
  | .zero, _     => .zero
  | _,     .zero => .zero
  | .one,  m     => m
  | m,     .one  => m
  | .many, .many => .many

/-! ## 1. Leyes de Semianillo Conmutativo de las Multiplicidades QTT -/

@[simp]
theorem addM_zero_left (m : Mult) : addM .zero m = m := by
  cases m <;> rfl

@[simp]
theorem addM_zero_right (m : Mult) : addM m .zero = m := by
  cases m <;> rfl

/-- TEOREMA 1 (Conmutatividad de la Suma de Multiplicidades): -/
theorem addM_comm (a b : Mult) : addM a b = addM b a := by
  cases a <;> cases b <;> rfl

/-- TEOREMA 2 (Asociatividad de la Suma de Multiplicidades): -/
theorem addM_assoc (a b c : Mult) : addM (addM a b) c = addM a (addM b c) := by
  cases a <;> cases b <;> cases c <;> rfl

@[simp]
theorem mulM_zero_left (m : Mult) : mulM .zero m = .zero := by
  cases m <;> rfl

@[simp]
theorem mulM_zero_right (m : Mult) : mulM m .zero = .zero := by
  cases m <;> rfl

@[simp]
theorem mulM_one_left (m : Mult) : mulM .one m = m := by
  cases m <;> rfl

@[simp]
theorem mulM_one_right (m : Mult) : mulM m .one = m := by
  cases m <;> rfl

/-- TEOREMA 3 (Conmutatividad del Producto de Multiplicidades): -/
theorem mulM_comm (a b : Mult) : mulM a b = mulM b a := by
  cases a <;> cases b <;> rfl

/-- TEOREMA 4 (Asociatividad del Producto de Multiplicidades): -/
theorem mulM_assoc (a b c : Mult) : mulM (mulM a b) c = mulM a (mulM b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-- TEOREMA 5 (Distributividad del Producto sobre la Suma en QTT):
    `π · (ρ₁ + ρ₂) = (π · ρ₁) + (π · ρ₂)` -/
theorem mulM_addM_distrib (p r1 r2 : Mult) :
    mulM p (addM r1 r2) = addM (mulM p r1) (mulM p r2) := by
  cases p <;> cases r1 <;> cases r2 <;> rfl

/-! ## 2. Álgebra de Contextos Cuantitativos y Borrado Garantizado de Tipos (`0`-Erasure) -/

/-- Escala todo un vector de usos de contexto `Γ : List Mult` por la multiplicidad `π` -/
@[simp]
def scaleCtx (π : Mult) : List Mult → List Mult
  | []      => []
  | m :: ms => mulM π m :: scaleCtx π ms

/-- Vector de usos nulo de la misma longitud que `Γ` (ninguna variable se consume en runtime) -/
@[simp]
def zeroCtx : List Mult → List Mult
  | []      => []
  | _ :: ms => .zero :: zeroCtx ms

/-- TEOREMA 6 (Invariante de Borrado Estático de Tipos en QTT):
    Cuando el verificador de tipos entra a comprobar una expresión en posición de tipo (`π = 0`),
    escalar cualquier contexto `Γ` por `.zero` produce el contexto idénticamente cero `zeroCtx Γ`.
    ¡Por eso usar una variable lineal `x :₁ A` dentro de un tipo dependiente `B(x)` NO consume
    el recurso lineal `x` en tiempo de ejecución! -/
theorem scaleCtx_zero_eq_zeroCtx (Γ : List Mult) :
    scaleCtx .zero Γ = zeroCtx Γ := by
  induction Γ with
  | nil          => rfl
  | cons m ms ih =>
    dsimp [scaleCtx, zeroCtx]
    rw [ih]

end Mult
end LeanTT.M61
