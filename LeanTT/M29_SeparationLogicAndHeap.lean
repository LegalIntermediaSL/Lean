/-!
# Módulo 29: Lógica de Separación (*Separation Logic*) y Razonamiento Modular sobre el Heap
## Ámbito: Verificación de Sistemas, Punteros y Concurrencia (Inspirado en `iris-lean`)

La **Lógica de Separación** (Reynolds, O'Hearn, Ishtiaq, 2001 — y su evolución de orden superior
**Iris** formalizada en `Verified-zkEVM/iris-lean`) resuelve el problema del *aliasing* de
punteros introduciendo la **Conjunción Separadora (`P ∗ Q`)**:
- Una aserción `P ∗ Q` se cumple en una memoria `h : Heap` si `h` puede dividirse en **dos
  sub-heaps de dominios disjuntos** `h1 ⊎ h2` tales que `P` se cumple en `h1` y `Q` en `h2`.
-/

namespace LeanTT.M29

abbrev Addr := Nat
abbrev Val  := Nat

/-- Un `Heap` finito representado como una función parcial `Addr → Option Val` -/
abbrev Heap := Addr → Option Val

namespace Heap

def empty : Heap := fun _ => none

def singleton (a : Addr) (v : Val) : Heap :=
  fun x => if x = a then some v else none

/-- Dos heaps `h1` y `h2` son disjuntos si ninguna dirección está asignada en ambos a la vez -/
def Disjoint (h1 h2 : Heap) : Prop :=
  ∀ a : Addr, h1 a = none ∨ h2 a = none

infix:50 " ⊥ₕ " => Disjoint

/-- Unión de dos heaps (`h1 ∪ₕ h2`) dando preferencia a `h1` cuando está definido -/
def union (h1 h2 : Heap) : Heap :=
  fun a =>
    match h1 a with
    | some v => some v
    | none   => h2 a

infixl:65 " ∪ₕ " => union

theorem disjoint_symm {h1 h2 : Heap} (hd : h1 ⊥ₕ h2) : h2 ⊥ₕ h1 := by
  intro a
  cases hd a with
  | inl h => exact Or.inr h
  | inr h => exact Or.inl h

/-- Si dos heaps son disjuntos, su unión `h1 ∪ₕ h2` es conmutativa! -/
theorem union_comm_of_disjoint {h1 h2 : Heap} (hd : h1 ⊥ₕ h2) :
    (h1 ∪ₕ h2) = (h2 ∪ₕ h1) := by
  funext a
  dsimp [union]
  rcases hd a with h1none | h2none
  · rw [h1none]
    cases h2 a <;> rfl
  · rw [h2none]
    cases h1 a <;> rfl

end Heap

/-! ## Aserciones de la Lógica de Separación (`HeapProp`) -/

abbrev HeapProp := Heap → Prop

/-- `emp`: El heap está completamente vacío -/
def emp : HeapProp :=
  fun h => h = Heap.empty

/-- `a ↦ v` (*Points-to*): El heap contiene única y exclusivamente la celda `a` con valor `v` -/
def pointsTo (a : Addr) (v : Val) : HeapProp :=
  fun h => h = Heap.singleton a v

infix:60 " ↦ₕ " => pointsTo

/-- Conjunción Separadora `P ∗ Q` (*Separating Conjunction*):
    El heap `h` se descompone en dos porciones disjuntas `h1 ⊥ₕ h2` donde `P h1` y `Q h2`. -/
def sepConj (P Q : HeapProp) : HeapProp :=
  fun h => ∃ h1 h2 : Heap, (h1 ⊥ₕ h2) ∧ (h = h1 ∪ₕ h2) ∧ P h1 ∧ Q h2

infixr:70 " ∗ " => sepConj

/-- Implicación de Aserciones (`P ⊢ₛ Q`) -/
def Entails (P Q : HeapProp) : Prop :=
  ∀ h : Heap, P h → Q h

infix:50 " ⊢ₛ " => Entails

/-! ## Teoremas Fundamentales de la Lógica de Separación -/

/-- 1. Conmutatividad de la Conjunción Separadora: `P ∗ Q ⊢ₛ Q ∗ P` -/
theorem sepConj_comm (P Q : HeapProp) : (P ∗ Q) ⊢ₛ (Q ∗ P) := by
  intro h ⟨h1, h2, hdisj, heq, hp, hq⟩
  refine ⟨h2, h1, Heap.disjoint_symm hdisj, ?_, hq, hp⟩
  rw [heq, Heap.union_comm_of_disjoint hdisj]

/-- 2. Unidad Izquierda de `emp`: `emp ∗ P ⊢ₛ P` -/
theorem emp_sepConj (P : HeapProp) : (emp ∗ P) ⊢ₛ P := by
  intro h ⟨h1, h2, _, heq, hemp, hp⟩
  dsimp [emp] at hemp
  subst hemp
  have hunion : (Heap.empty ∪ₕ h2) = h2 := by
    funext a
    rfl
  rw [heq, hunion]
  exact hp

/-- 3. Regla de Monotonía del Marco (*Frame Monotonicity*):
    Si `P ⊢ₛ P'`, entonces para cualquier marco `R` disjunto se cumple `P ∗ R ⊢ₛ P' ∗ R`. -/
theorem frame_mono {P P' : HeapProp} (R : HeapProp) (himp : P ⊢ₛ P') :
    (P ∗ R) ⊢ₛ (P' ∗ R) := by
  intro h ⟨h1, h2, hdisj, heq, hp, hr⟩
  exact ⟨h1, h2, hdisj, heq, himp h1 hp, hr⟩

/-- 4. Exclusión Mutua de Punteros (*Disjoint Points-To*):
    Si `(a ↦ₕ v1) ∗ (b ↦ₕ v2)` se cumple en algún heap `h`, entonces las direcciones
    `a` y `b` DEBEN ser distintas (`a ≠ b`)! -/
theorem pointsTo_sep_ne {a b : Addr} {v1 v2 : Val} {h : Heap}
    (hs : ((a ↦ₕ v1) ∗ (b ↦ₕ v2)) h) : a ≠ b := by
  intro hab
  subst hab
  rcases hs with ⟨h1, h2, hdisj, _, rfl, rfl⟩
  have hd := hdisj a
  dsimp [Heap.singleton] at hd
  rw [if_pos rfl, if_pos rfl] at hd
  rcases hd with h1 | h2 <;> contradiction

end LeanTT.M29
