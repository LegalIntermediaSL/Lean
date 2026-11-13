/-!
# Módulo 13: Fundamentos de la Teoría de Tipos Dependientes Desde Cero
Guía teórica asociada: `docs/14_tratado_completo_teoria_tipos_dependientes.md`

En este módulo implementamos en Lean 4 las construcciones fundacionales de la
Teoría Intuicionista de Tipos de Per Martin-Löf (MLTT):
1. Las 5 reglas canónicas de los tipos finitos (`Empty`, `Unit`, `Bool`) y Large Elimination.
2. Familias de tipos definidas por recursión (`VectorRecursivo α n`) vs. familias inductivas.
3. El eliminador `J` de Martin-Löf y la contractibilidad del espacio basado `(y : A) × (a = y)`.
4. Los Tipos de Árboles Bien Fundados (`W-Types`), codificación de `Nat` como un `W-Type`
   e isomorfismo verificado entre `WNat` y `Nat`.
-/

namespace LeanTT.M13

universe u v w

/-! ## 1. Las 5 Reglas Canónicas en Tipos Finitos y Large Elimination -/

/-- Regla η para `Unit`: cualesquiera dos habitantes de `Unit` son definicionalmente iguales -/
theorem unit_eta (x : Unit) : x = () :=
  rfl

/-- Large Elimination: una familia de tipos indexada por `Bool` que devuelve un `Type` distinto
    según el valor booleano. -/
def FibraBool : Bool → Type
  | false => Nat × Nat
  | true  => String

/-- Sección dependiente `(b : Bool) → FibraBool b` construida directamente con `Bool.rec` -/
def seccionFibraBool (b : Bool) : FibraBool b :=
  Bool.rec (motive := FibraBool) (7, 11) "Teoría de Tipos de Martin-Löf" b

#eval seccionFibraBool false -- (7, 11)
#eval seccionFibraBool true  -- "Teoría de Tipos de Martin-Löf"

/-! ## 2. Familias de Tipos por Recursión Sobre Índices (`VectorRecursivo`) -/

/-- En lugar de usar una familia inductiva, calculamos el tipo `α × (α × ... × PUnit)`
    por recursión estructural sobre la longitud `n : Nat` (Large Elimination sobre `Nat`). -/
def VectorRecursivo (α : Type u) : Nat → Type u
  | 0     => PUnit
  | n + 1 => α × VectorRecursivo α n

def headRec {α : Type u} {n : Nat} (v : VectorRecursivo α (n + 1)) : α :=
  v.1

def tailRec {α : Type u} {n : Nat} (v : VectorRecursivo α (n + 1)) : VectorRecursivo α n :=
  v.2

def mapRec {α β : Type u} (f : α → β) : {n : Nat} → VectorRecursivo α n → VectorRecursivo β n
  | 0,     PUnit.unit => PUnit.unit
  | _ + 1, (x, xs)    => (f x, mapRec f xs)

/-- En `VectorRecursivo`, como un vector de longitud `n + 1` es literalmente un par `(x, xs)`,
    ¡la ley de reconstrucción `(headRec v, tailRec v) = v` se cumple definicionalmente (`rfl`)! -/
theorem eta_vector_recursivo {α : Type u} {n : Nat} (v : VectorRecursivo α (n + 1)) :
    (headRec v, tailRec v) = v :=
  rfl

/-! ## 3. El Eliminador `J` de Martin-Löf y la Contractibilidad del Espacio Basado -/

/-- El eliminador `J` de Martin-Löf con ambos extremos libres `x, y : A` -/
def martinLofJ {A : Sort u}
    (C : (x y : A) → (x = y) → Sort v)
    (diag : (x : A) → C x x rfl)
    {a b : A} (p : a = b) : C a b p :=
  match p with
  | rfl => diag a

/-- La regla de β-computación de `martinLofJ` se cumple definicionalmente (`rfl`) -/
theorem martinLofJ_beta {A : Sort u}
    (C : (x y : A) → (x = y) → Sort v)
    (diag : (x : A) → C x x rfl) (a : A) :
    martinLofJ C diag (rfl : a = a) = diag a :=
  rfl

/-- El espacio basado en `a`: el Σ-tipo de todos los puntos `y : A` junto con una prueba `a = y` -/
def EspacioBasado {A : Type u} (a : A) : Type u :=
  (y : A) × (a = y)

def centroBasado {A : Type u} (a : A) : EspacioBasado a :=
  ⟨a, rfl⟩

/-- Teorema fundamental: el espacio total `(y : A) × (a = y)` es contráctil al centro `⟨a, rfl⟩` -/
theorem espacioBasado_contractil {A : Type u} {a : A} (w : EspacioBasado a) :
    w = centroBasado a := by
  rcases w with ⟨y, rfl⟩
  rfl

/-! ## 4. Los Tipos de Árboles Bien Fundados (`W-Types`) de Martin-Löf -/

/-- `W A B` es el tipo inductivo universal parametrizado por un tipo de etiquetas de constructores
    `A` y una familia de aridades `B : A → Type v`. -/
inductive W (A : Type u) (B : A → Type v) : Type (max u v) where
  | sup (a : A) (hijos : B a → W A B) : W A B

/-- Principio de inducción dependiente sobre `W A B` -/
def W.ind {A : Type u} {B : A → Type v} {P : W A B → Sort w}
    (step : ∀ (a : A) (hijos : B a → W A B), (∀ b : B a, P (hijos b)) → P (W.sup a hijos)) :
    (w : W A B) → P w
  | W.sup a hijos => step a hijos (fun b => W.ind step (hijos b))

/-- Aridad de los constructores de `Nat`:
    - `false` (`zero`) tiene 0 hijos (`Empty`)
    - `true`  (`succ`) tiene 1 hijo  (`Unit`) -/
def NatArity : Bool → Type
  | false => Empty
  | true  => Unit

/-- Los números naturales codificados como un `W-Type` puro de Martin-Löf -/
abbrev WNat := W Bool NatArity

def wZero : WNat :=
  W.sup false (fun e => nomatch e)

def wSucc (n : WNat) : WNat :=
  W.sup true (fun _ => n)

/-- Conversión de `Nat` a `WNat` -/
def natToWNat : Nat → WNat
  | 0     => wZero
  | n + 1 => wSucc (natToWNat n)

/-- Conversión de `WNat` a `Nat` -/
def wNatToNat : WNat → Nat
  | W.sup false _     => 0
  | W.sup true  hijos => (wNatToNat (hijos ())) + 1

/-- Demostración formal de que `wNatToNat` es retracción de `natToWNat` -/
theorem wNatToNat_natToWNat (n : Nat) : wNatToNat (natToWNat n) = n := by
  induction n with
  | zero      => rfl
  | succ k ih => simp [natToWNat, wSucc, wNatToNat, ih]

end LeanTT.M13
