/-!
# Módulo 23: Teoría de Tipos Homotópica (HoTT) Sintética — Álgebra de Caminos y Equivalencias
## Ámbito: Topología Algebraica Sintética y Fundamentos Homotópicos

En la Teoría de Tipos Homotópica (HoTT):
- Un **tipo** `A` se interpreta como un **espacio topológico** (o un $\infty$-grupoide).
- Un **término** `a : A` es un **punto** del espacio.
- Una **identificación** `p : Path A a b` es un **camino continuo** desde `a` hasta `b`.
- Una **función** `f : A → B` es una aplicación continua, y su acción `ap f p : Path B (f a) (f b)`
  envía caminos en `A` a caminos en `B`.

Aquí definimos un tipo de caminos `Path` en `Type u` y demostramos todas las leyes del
**grupoide fundamental** (unidades, asociatividad, inversos y funtorialidad de `ap`).
-/

namespace LeanTT.M23

universe u v

/-- Definimos `Path α a b` como una familia inductiva en `Type u` (relevante a las pruebas) -/
inductive Path {α : Type u} (a : α) : α → Type u where
  | refl : Path a a

infix:50 " ≡ₚ " => Path

namespace Path

/-- Inverso de un camino (`p⁻¹` recorre el camino `p` en sentido contrario) -/
def symm {α : Type u} {a b : α} : (a ≡ₚ b) → (b ≡ₚ a)
  | .refl => .refl

postfix:max "⁻¹ᵖ" => Path.symm

/-- Concatenación de dos caminos (`p • q`) -/
def trans {α : Type u} {a b c : α} : (a ≡ₚ b) → (b ≡ₚ c) → (a ≡ₚ c)
  | .refl, .refl => .refl

infixl:65 " • " => Path.trans

/-! ## 1. Las Leyes del Grupoide Fundamental de un Tipo -/

theorem trans_refl_left {α : Type u} {a b : α} (p : a ≡ₚ b) :
    (.refl • p) = p := by
  cases p; rfl

theorem trans_refl_right {α : Type u} {a b : α} (p : a ≡ₚ b) :
    (p • .refl) = p := by
  cases p; rfl

theorem trans_assoc {α : Type u} {a b c d : α}
    (p : a ≡ₚ b) (q : b ≡ₚ c) (r : c ≡ₚ d) :
    ((p • q) • r) = (p • (q • r)) := by
  cases p; cases q; cases r; rfl

theorem symm_trans {α : Type u} {a b : α} (p : a ≡ₚ b) :
    (p⁻¹ᵖ • p) = .refl := by
  cases p; rfl

theorem trans_symm {α : Type u} {a b : α} (p : a ≡ₚ b) :
    (p • p⁻¹ᵖ) = .refl := by
  cases p; rfl

theorem symm_symm {α : Type u} {a b : α} (p : a ≡ₚ b) :
    (p⁻¹ᵖ)⁻¹ᵖ = p := by
  cases p; rfl

/-! ## 2. Acción de una Función sobre Caminos (`ap`) y Funtorialidad -/

/-- Toda función `f : α → β` actúa continuamente sobre los caminos de `α` -/
def ap {α : Type u} {β : Type v} (f : α → β) {a b : α} : (a ≡ₚ b) → (f a ≡ₚ f b)
  | .refl => .refl

/-- `ap` preserva la concatenación de caminos: `ap f (p • q) = ap f p • ap f q` -/
theorem ap_trans {α : Type u} {β : Type v} (f : α → β) {a b c : α}
    (p : a ≡ₚ b) (q : b ≡ₚ c) :
    ap f (p • q) = (ap f p) • (ap f q) := by
  cases p; cases q; rfl

/-- `ap` conmuta con la inversión de caminos: `ap f (p⁻¹ᵖ) = (ap f p)⁻¹ᵖ` -/
theorem ap_symm {α : Type u} {β : Type v} (f : α → β) {a b : α} (p : a ≡ₚ b) :
    ap f (p⁻¹ᵖ) = (ap f p)⁻¹ᵖ := by
  cases p; rfl

/-! ## 3. Homotopías (`f ∼ g`) y Equivalencias de Tipos (`α ≃ β`) -/

/-- Una homotopía entre dos funciones `f, g : (x : α) → β x` es una familia continua
    de caminos `H x : f x ≡ₚ g x` para cada punto `x : α`. -/
def Homotopy {α : Type u} {β : α → Type v} (f g : (x : α) → β x) : Type (max u v) :=
  (x : α) → (f x ≡ₚ g x)

infix:50 " ∼ " => Homotopy

/-- Una equivalencia cuasi-inversa entre dos tipos `α` y `β` -/
structure Equiv (α : Type u) (β : Type v) where
  toFun   : α → β
  invFun  : β → α
  leftInv : (fun x => invFun (toFun x)) ∼ (fun x => x)
  rightInv: (fun y => toFun (invFun y)) ∼ (fun y => y)

infix:25 " ≃ₕ " => Equiv

/-- La involución `Bool.not` es una equivalencia `Bool ≃ₕ Bool` distinta de la identidad -/
def equivNegBool : Bool ≃ₕ Bool where
  toFun    := Bool.not
  invFun   := Bool.not
  leftInv  := fun b => by cases b <;> exact .refl
  rightInv := fun b => by cases b <;> exact .refl

end Path
end LeanTT.M23
