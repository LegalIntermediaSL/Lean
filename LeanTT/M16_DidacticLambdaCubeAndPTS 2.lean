/-!
# Módulo 16 (Especialmente Didáctico): Las 8 Esquinas del Cubo de Barendregt en Lean 4
## Un Ejemplo Ejecutable para Cada Vértice del Cubo

El Cubo de Barendregt clasifica los sistemas de tipos según qué combinaciones de las
3 extensiones sobre el cálculo simplemente tipado (`λ→`) se permiten:
- **P (Polimorfismo):** Términos que dependen de Tipos (`∀ α : Type, ...`)
- **ω (Operadores de tipos):** Tipos que dependen de Tipos (`Type → Type`)
- **D (Tipos Dependientes):** Tipos que dependen de Términos (`Nat → Type`)

Las $2^3 = 8$ combinaciones forman los 8 vértices del cubo, y todos viven dentro de Lean 4.
-/

namespace LeanTT.M16

/-! ## Vértice 1: `λ→` (Cálculo Lambda Simplemente Tipado — Sin P, sin ω, sin D)
Solo existen tipos base (`Nat`, `Bool`) y funciones de términos a términos (`A → B`). -/
def v1_stlc (x : Nat) (y : Nat) : Nat :=
  x + y * 2

/-! ## Vértice 2: `λ2` / Sistema F (Con P, sin ω, sin D)
Añade funciones que reciben un **tipo** y devuelven un **término** (Polimorfismo paramétrico). -/
def v2_systemF : (α : Type) → (β : Type) → α → β → α × β :=
  fun _ _ a b => (a, b)

#eval v2_systemF Nat String 42 "Sistema F"

/-! ## Vértice 3: `λω_` (Sin P, con ω, sin D)
Añade funciones que reciben un **tipo** y devuelven un **tipo** (Constructores de tipos),
pero sin cuantificar polimórficamente en los términos. -/
def Diagonal (α : Type) : Type := α × α
def DobleDiagonal (α : Type) : Type := Diagonal (Diagonal α)

def v3_lamOmega_ : DobleDiagonal Nat :=
  ((1, 2), (3, 4))

/-! ## Vértice 4: `λω` / Sistema Fω (Con P y con ω, sin D)
Combina polimorfismo paramétrico con constructores de tipos de orden superior `F : Type → Type`
(es el núcleo de lenguajes como Haskell con `RankNTypes`). -/
def v4_systemF_omega (F : Type → Type) (mapF : ∀ α β, (α → β) → F α → F β)
    (α : Type) (f : α → α) (x : F α) : F α :=
  mapF α α (fun a => f (f a)) x

#eval v4_systemF_omega List (@List.map) Nat (· + 10) [1, 2, 3] -- [21, 22, 23]

/-! ## Vértice 5: `λP` / Logical Framework LF (Sin P, sin ω, con D)
Añade **tipos que dependen de términos** (`Nat → Type`), pero sin polimorfismo sobre tipos. -/
inductive VecNat : Nat → Type where
  | nil  : VecNat 0
  | cons : {n : Nat} → Nat → VecNat n → VecNat (n + 1)

def v5_lf : VecNat 2 :=
  .cons 10 (.cons 20 .nil)

/-! ## Vértice 6: `λP2` (Con P y con D, sin ω)
Combina tipos dependientes de términos con polimorfismo paramétrico sobre tipos `α : Type`. -/
inductive VecPoly (α : Type) : Nat → Type where
  | nil  : VecPoly α 0
  | cons : {n : Nat} → α → VecPoly α n → VecPoly α (n + 1)

def v6_lamP2 : ∀ (α : Type) (n : Nat) (x : α), VecPoly α n → VecPoly α (n + 1) :=
  fun _ _ x xs => .cons x xs

/-! ## Vértice 7: `λPω_` (Con ω y con D, sin P en términos)
Operadores de tipos de orden superior que además dependen de términos (`(Nat → Type) → Nat → Type`). -/
def DesplazarIndice (Familia : Nat → Type) (n : Nat) : Type :=
  Familia (n + 1)

def v7_lamPOmega_ : DesplazarIndice VecNat 0 :=
  .cons 99 .nil

/-! ## Vértice 8: `λC` / Cálculo de Construcciones (Con P, con ω y con D)
La cúspide del cubo: términos y tipos pueden depender tanto de términos como de tipos
y de operadores de familias dependientes arbitrarios. -/
def v8_calculusOfConstructions
    (α : Type)
    (Familia : α → Nat → Type)
    (semilla : (x : α) → Familia x 0)
    (paso    : (x : α) → (k : Nat) → Familia x k → Familia x (k + 1))
    (x : α) : (n : Nat) → Familia x n
  | 0     => semilla x
  | k + 1 => paso x k (v8_calculusOfConstructions α Familia semilla paso x k)

end LeanTT.M16
