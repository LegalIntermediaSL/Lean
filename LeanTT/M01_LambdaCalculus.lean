/-!
# Módulo 01: Cálculo Lambda, Reducciones del Kernel y el Cubo de Barendregt
Guía teórica asociada: `docs/01_calculo_lambda.md`

En este módulo exploramos:
1. Abstracción y aplicación lambda en Lean 4.
2. Las seis reducciones del kernel (`β`, `η`, `δ`, `ι`, `ζ` y proyecciones).
3. El Cálculo Combinatorio `S`, `K`, `I` y su equivalencia computacional.
4. Codificaciones de Church (Booleanos, Pares y Numerales en el Sistema F).
5. Los cuatro ejes del Cubo de Barendregt expresados directamente en Lean 4.
-/

namespace LeanTT.M01

universe u v w

/-! ## 1. Abstracción, Aplicación y Currificación -/

/-- En Lean 4, `fun x => e` y `λ x => e` son notaciones idénticas para la abstracción lambda. -/
def sucesor : Nat → Nat :=
  fun x => x + 1

/-- Función de múltiples argumentos mediante currificación:
    `Nat → Nat → Nat` se asocia por la derecha como `Nat → (Nat → Nat)`. -/
def sumaCurried : Nat → (Nat → Nat) :=
  fun x => fun y => x + y

/-- Currificación y descurrificación explícita entre `(α × β → γ)` y `(α → β → γ)`. -/
def curry {α : Type u} {β : Type v} {γ : Type w} (f : α × β → γ) : α → β → γ :=
  fun a b => f (a, b)

def uncurry {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) : α × β → γ :=
  fun p => f p.1 p.2

/-- Demostración por reflexividad (`rfl`, que usa β y η reducción en el kernel)
    de que `curry` y `uncurry` son inversas mutuas. -/
theorem curry_uncurry {α : Type u} {β : Type v} {γ : Type w} (f : α → β → γ) :
    curry (uncurry f) = f :=
  rfl

/-! ## 2. Las Reducciones del Kernel de Lean (`rfl` como Verificador de Conversión) -/

/-- 1. β-reducción: `((fun x => x + 10) 5)` se reduce definicionalmente a `15`. -/
example : (fun x : Nat => x + 10) 5 = 15 := rfl

/-- 2. η-conversión: `fun x => f x` es definicionalmente igual a `f`. -/
example (α β : Type) (f : α → β) : (fun x => f x) = f := rfl

/-- 3. ζ-reducción: las ligaduras `let` se sustituyen automáticamente en el kernel. -/
example : (let x := 6; x * x) = 36 := rfl

/-- 4. ι-reducción: el recursor `Nat.rec` se reduce al aplicarse a `Nat.succ`. -/
example (z : Nat) (s : Nat → Nat → Nat) (n : Nat) :
    (Nat.rec z s (Nat.succ n) : Nat) = s n (Nat.rec z s n) := rfl

/-! ## 3. Cálculo Combinatorio SKI -/

/-- Combinador Identidad `I = λx. x` -/
def I {α : Type u} : α → α :=
  fun x => x

/-- Combinador Constante `K = λx. λy. x` -/
def K {α : Type u} {β : Type v} : α → β → α :=
  fun x _ => x

/-- Combinador de Fusión/Sustitución `S = λf. λg. λx. f x (g x)` -/
def S {α : Type u} {β : Type v} {γ : Type w} :
    (α → β → γ) → (α → β) → α → γ :=
  fun f g x => f x (g x)

/-- Combinador de Composición `B = λf. λg. λx. f (g x)` -/
def B {α : Type u} {β : Type v} {γ : Type w} :
    (β → γ) → (α → β) → α → γ :=
  fun f g x => f (g x)

/-- Combinador de Permutación `C = λf. λx. λy. f y x` -/
def C {α : Type u} {β : Type v} {γ : Type w} :
    (α → β → γ) → β → α → γ :=
  fun f y x => f x y

/-- Teorema clásico de Schönfinkel-Curry: `S K K` se β-reduce a `I`. -/
theorem skk_eq_i (α : Type u) (x : α) : S K (@K α α) x = I x :=
  rfl

/-- El combinador de composición `B` puede definirse a partir de `S` y `K`:
    `B = S (K S) K`. Verificado por β-reducción pura (`rfl`). -/
theorem b_from_sk {α β γ : Type} (f : β → γ) (g : α → β) (x : α) :
    S (K S) K f g x = B f g x :=
  rfl

/-! ## 4. Codificaciones de Church en el Sistema F (`λ2`) -/

/-- Booleanos de Church polimórficos: eligen entre dos alternativas de tipo `α`. -/
def ChurchBool : Type 1 := ∀ (α : Type), α → α → α

def cTrue : ChurchBool  := fun _ t _ => t
def cFalse : ChurchBool := fun _ _ f => f

def cNot (b : ChurchBool) : ChurchBool :=
  fun α t f => b α f t

def cAnd (b1 b2 : ChurchBool) : ChurchBool :=
  fun α t f => b1 α (b2 α t f) f

example : cAnd cTrue cFalse = cFalse := rfl
example : cNot cFalse = cTrue := rfl

/-- Numerales de Church en el Sistema F: `∀ α, (α → α) → α → α` -/
def ChurchNat : Type 1 := ∀ (α : Type), (α → α) → α → α

def cZero : ChurchNat :=
  fun _ _ x => x

def cSucc (n : ChurchNat) : ChurchNat :=
  fun α f x => f (n α f x)

def cAdd (m n : ChurchNat) : ChurchNat :=
  fun α f x => m α f (n α f x)

def cMul (m n : ChurchNat) : ChurchNat :=
  fun α f x => m α (n α f) x

def cExp (base exp : ChurchNat) : ChurchNat :=
  fun α => exp (α → α) (base α)

/-- Puente entre `ChurchNat` y el tipo inductivo `Nat` de Lean -/
def ChurchNat.toNat (n : ChurchNat) : Nat :=
  n Nat Nat.succ 0

def cTwo : ChurchNat   := cSucc (cSucc cZero)
def cThree : ChurchNat := cSucc cTwo

/-- En numerales de Church, `2 + 3 = 5` y `2 * 3 = 6` son verdades definicionales (`rfl`). -/
example : (cAdd cTwo cThree).toNat = 5 := rfl
example : (cMul cTwo cThree).toNat = 6 := rfl
example : (cExp cTwo cThree).toNat = 8 := rfl

/-! ## 5. Los Cuatro Ejes del Cubo de Barendregt en Lean 4 -/

/-- Eje 1 `(Term → Term)` — STLC (`λ→`): función de términos a términos -/
def eje1_term_to_term : Nat → Nat :=
  fun n => n * 2

/-- Eje 2 `(Type → Term)` — Sistema F (`λ2`): función de tipos a términos -/
def eje2_type_to_term : (α : Type) → α → α × α :=
  fun _ x => (x, x)

/-- Eje 3 `(Type → Type)` — `λω`: operador de tipos a tipos -/
def eje3_type_to_type : Type → Type :=
  fun α => List (α × α)

/-- Eje 4 `(Term → Type)` — `λP`: familia de tipos que depende de un término `n : Nat` -/
def eje4_term_to_type : Nat → Type
  | 0     => Unit
  | n + 1 => Nat × eje4_term_to_type n

/-- Ejemplo de tupla de longitud dependiente `eje4_term_to_type 3` -/
def tuplaDeTres : eje4_term_to_type 3 :=
  (10, (20, (30, ())))

end LeanTT.M01
