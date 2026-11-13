/-!
# Módulo 26: Polimorfismo del Sistema F, Tipos Existenciales y Parametricidad de Reynolds
## Ámbito: Fundamentos de Lenguajes de Programación y "Theorems for Free" (Wadler / Reynolds)

En el Sistema F (`λ2` de Girard-Reynolds), el polimorfismo universal `∀ (α : Type), ...` permite:
1. Codificar **Tipos Abstractos de Datos (ADTs / Tipos Existenciales)** `∃ α, T α` usando únicamente
   cuantificación universal (`∀ γ, (∀ α, T α → γ) → γ`).
2. Obtener **Teoremas Gratis (*Theorems for Free*)**: el tipo de una función polimórfica restringe
   tan fuertemente su comportamiento que podemos deducir ecuaciones sobre ella.
-/

namespace LeanTT.M26

universe u v

/-! ## 1. Codificación Impredicativa de Tipos Existenciales (Paquetes de Datos Abstractos) -/

/-- En el Sistema F, el tipo existencial `∃ (α : Type), Ops α` se codifica como:
    `∀ (γ : Type), (∀ (α : Type), Ops α → γ) → γ`.
    Quien construye el paquete elige la representación interna `α`, pero el cliente `γ`
    está obligado a funcionar para *cualquier* `α`, ocultando la implementación (encapsulación). -/
def ExistentialPackage (Ops : Type → Type) : Type 1 :=
  ∀ (γ : Type), (∀ (α : Type), Ops α → γ) → γ

def pack {Ops : Type → Type} (α : Type) (impl : Ops α) : ExistentialPackage Ops :=
  fun _ k => k α impl

/-- Interfaz de una Pila Abstracta (`StackOps σ`) parametrizada por su tipo de estado interno `σ` -/
structure StackOps (σ : Type) where
  empty : σ
  push  : Nat → σ → σ
  pop   : σ → Option (Nat × σ)

/-- Implementación 1 de la Pila Abstracta usando `List Nat` como tipo interno `σ` -/
def listStackImpl : StackOps (List Nat) where
  empty     := []
  push x xs := x :: xs
  pop
    | []      => none
    | x :: xs => some (x, xs)

/-- Empaquetamos la implementación ocultando que por dentro es una `List Nat` -/
def abstractStack : ExistentialPackage StackOps :=
  pack (List Nat) listStackImpl

/-- Un cliente que usa el paquete existencial sin saber que el tipo interno es `List Nat` -/
def usarPilaAbstracta (pkg : ExistentialPackage StackOps) : Option Nat :=
  pkg (Option Nat) (fun _ ops =>
    let s0 := ops.empty
    let s1 := ops.push 10 s0
    let s2 := ops.push 25 s1
    match ops.pop s2 with
    | some (top, _) => some top
    | none          => none)

#eval usarPilaAbstracta abstractStack -- some 25

/-! ## 2. Parametricidad Relacional de Reynolds ("Theorems for Free") -/

/-- Una función polimórfica `f : ∀ α, List α → List α` (como `reverse`, `tail`, `take n`,
    o duplicar elementos) cumple el "Teorema Gratis" de que **conmuta con `List.map g`**
    para cualquier función `g : α → β`:
    `List.map g (f α xs) = f β (List.map g xs)`.
    Expresamos esta propiedad de naturalidad como un predicado explícito: -/
def EsNaturalEnListas (f : ∀ (α : Type), List α → List α) : Prop :=
  ∀ (α β : Type) (g : α → β) (xs : List α),
    List.map g (f α xs) = f β (List.map g xs)

/-- Demostración formal de que `List.reverse` satisface la condición de naturalidad de Reynolds -/
theorem reverse_es_natural : EsNaturalEnListas (@List.reverse) := by
  intro α β g xs
  simp [List.map_reverse]

/-- Si dos funciones polimórficas `f1` y `f2` son naturales, su composición también lo es -/
theorem comp_es_natural (f1 f2 : ∀ (α : Type), List α → List α)
    (h1 : EsNaturalEnListas f1) (h2 : EsNaturalEnListas f2) :
    EsNaturalEnListas (fun α xs => f1 α (f2 α xs)) := by
  intro α β g xs
  rw [h1 α β g (f2 α xs)]
  rw [h2 α β g xs]

end LeanTT.M26
