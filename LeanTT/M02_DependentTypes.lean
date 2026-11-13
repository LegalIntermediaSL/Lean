/-!
# Módulo 02: Teoría de Tipos Dependientes — Tipos Π, Tipos Σ, Subtipos y `printf` Tipado
Guía teórica asociada: `docs/02_tipos_dependientes_pi_sigma.md`

En este módulo exploramos:
1. Tipos Producto Dependiente (`Π x : A, B x` / `(x : A) → B x`).
2. Tipos Suma Dependiente (`Σ x : A, B x` / `(x : A) × B x`).
3. Subtipos refinados `{ x : α // P x }` con borrado de pruebas en compilación.
4. Caso de estudio clásico: un `sprintf` estáticamente tipado cuyo número y tipo de
   argumentos dependen de la cadena de formato.
-/

namespace LeanTT.M02

universe u v

/-! ## 1. Tipos Producto Dependiente (Π-Types) -/

/-- Una familia de tipos indexada por un booleano -/
def BoolFamily : Bool → Type
  | true  => Nat
  | false => String

/-- Una función dependiente `(b : Bool) → BoolFamily b`:
    cuando `b = true` devuelve un `Nat`, y cuando `b = false` devuelve un `String`. -/
def valorPorDefecto : (b : Bool) → BoolFamily b
  | true  => 2026
  | false => "Lean 4 Dependent Types"

#eval valorPorDefecto true
#eval valorPorDefecto false

/-- El combinador `S` dependiente (generalización a Π-types del combinador `S` de SKI):
    Observa cómo el tipo del tercer argumento de `f` depende tanto de `x` como del valor `g x`. -/
def depS {α : Type u} {β : α → Type v} {γ : (x : α) → β x → Type u}
    (f : (x : α) → (y : β x) → γ x y)
    (g : (x : α) → β x) :
    (x : α) → γ x (g x) :=
  fun x => f x (g x)

/-! ## 2. Tipos Suma Dependiente (Σ-Types / Pares Dependientes) -/

/-- Un par dependiente `(b : Bool) × BoolFamily b` empaqueta la etiqueta booleana
    junto con un dato del tipo dictado por esa etiqueta. -/
def ejemploSigma1 : (b : Bool) × BoolFamily b :=
  ⟨true, 42⟩

def ejemploSigma2 : (b : Bool) × BoolFamily b :=
  ⟨false, "Hola Sigma"⟩

/-- Equivalencia fundamental (Axioma de Elección Constructivo / Currificación de Σ y Π):
    Una función que para todo `x : α` produce un par dependiente `(y : β x) × γ x y`
    es isomorfa a un par dependiente cuya primera componente es una función `f : (x : α) → β x`
    y cuya segunda componente es una función `(x : α) → γ x (f x)`. -/
def sigmaPiDistribute {α : Type u} {β : α → Type v} {γ : (x : α) → β x → Type u}
    (h : (x : α) → (y : β x) × γ x y) :
    (f : (x : α) → β x) × ((x : α) → γ x (f x)) :=
  ⟨fun x => (h x).fst, fun x => (h x).snd⟩

def sigmaPiUnDistribute {α : Type u} {β : α → Type v} {γ : (x : α) → β x → Type u}
    (p : (f : (x : α) → β x) × ((x : α) → γ x (f x))) :
    (x : α) → (y : β x) × γ x y :=
  fun x => ⟨p.fst x, p.snd x⟩

/-! ## 3. Subtipos `{ x : α // P x }` (Datos con Invariante en `Prop`) -/

/-- Tipo de números naturales estrictamente positivos -/
abbrev NatPos := { n : Nat // 0 < n }

/-- Tipo de números naturales pares -/
abbrev NatPar := { n : Nat // n % 2 = 0 }

/-- Constructor seguro de `NatPos` para `n + 1` -/
def succPos (n : Nat) : NatPos :=
  ⟨n + 1, Nat.zero_lt_succ n⟩

/-- La suma de dos números pares es par: la función construye el dato y la prueba a la vez -/
def sumaPares (a b : NatPar) : NatPar :=
  ⟨a.val + b.val, by
    have ha := a.property
    have hb := b.property
    omega⟩

#eval (sumaPares ⟨4, rfl⟩ ⟨6, rfl⟩).val -- 10

/-! ## 4. Caso de Estudio: `printf` Dependientemente Tipado -/

/-- Especificadores de formato para nuestro `printf` tipado -/
inductive Spec where
  | nat  : Spec             -- %d : espera un Nat
  | str  : Spec             -- %s : espera un String
  | lit  : String → Spec    -- texto literal

/-- Calcula el tipo de la función `printf` a partir de una lista de especificadores `List Spec`.
    ¡Esta es una función que recibe datos (`List Spec`) y devuelve un `Type`! -/
def PrintfType : List Spec → Type
  | []                => String
  | .nat :: rest      => Nat → PrintfType rest
  | .str :: rest      => String → PrintfType rest
  | .lit _ :: rest    => PrintfType rest

/-- Implementación recursiva dependiente que construye la función del tipo `PrintfType specs` -/
def printfAux (acc : String) : (specs : List Spec) → PrintfType specs
  | []             => acc
  | .nat :: rest   => fun (n : Nat)    => printfAux (acc ++ toString n) rest
  | .str :: rest   => fun (s : String) => printfAux (acc ++ s) rest
  | .lit s :: rest => printfAux (acc ++ s) rest

def printf (specs : List Spec) : PrintfType specs :=
  printfAux "" specs

/-- Ejemplo de formato: `"Usuario: %s (ID: %d)"`
    Observa que `printf formatoUsuario` tiene automáticamente el tipo `String → Nat → String`. -/
def formatoUsuario : List Spec :=
  [.lit "Usuario: ", .str, .lit " (ID: ", .nat, .lit ")"]

#check printf formatoUsuario -- String → Nat → String
#eval printf formatoUsuario "Ada Lovelace" 101

end LeanTT.M02
