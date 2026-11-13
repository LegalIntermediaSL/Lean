/-!
# Módulo 17: Estructuras de Datos Verificadas — Árboles Binarios de Búsqueda (BST)
## Ámbito: Ingeniería de Software Verificada y Estructuras de Datos

En este módulo implementamos un Árbol Binario de Búsqueda (`BST`) sobre `Nat` y demostramos
formalmente sus teoremas de corrección funcional:
1. Pertenencia `mem` e inserción `insert`.
2. Demostración de que todo elemento insertado pertenece al árbol resultante (`mem_insert_self`).
3. Demostración de que `insert` preserva todos los elementos previos (`mem_insert_of_mem`).
4. Espejo de un árbol binario (`mirror`) y demostración de que `mirror (mirror t) = t`.
-/

namespace LeanTT.M17

inductive Tree (α : Type) : Type where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α
  deriving Repr, DecidableEq

namespace Tree

/-- Número de nodos del árbol -/
@[simp]
def size {α : Type} : Tree α → Nat
  | .leaf       => 0
  | .node l _ r => 1 + l.size + r.size

/-- Imagen especular de un árbol binario -/
@[simp]
def mirror {α : Type} : Tree α → Tree α
  | .leaf       => .leaf
  | .node l x r => .node r.mirror x l.mirror

/-- Teorema: Invertir un árbol dos veces devuelve el árbol original -/
theorem mirror_mirror {α : Type} (t : Tree α) : t.mirror.mirror = t := by
  induction t with
  | leaf           => rfl
  | node l x r ihl ihr => simp [ihl, ihr]

/-- Teorema: `mirror` preserva exactamente el número de nodos -/
theorem size_mirror {α : Type} (t : Tree α) : t.mirror.size = t.size := by
  induction t with
  | leaf           => rfl
  | node l x r ihl ihr =>
    simp [ihl, ihr]
    omega

/-! ## Operaciones de Árbol Binario de Búsqueda (BST) sobre `Nat` -/

/-- Pertenencia general en un árbol binario -/
@[simp]
def mem (x : Nat) : Tree Nat → Prop
  | .leaf       => False
  | .node l v r => x = v ∨ mem x l ∨ mem x r

/-- Inserción en un árbol binario de búsqueda -/
@[simp]
def bstInsert (x : Nat) : Tree Nat → Tree Nat
  | .leaf => .node .leaf x .leaf
  | .node l v r =>
    if x < v then
      .node (bstInsert x l) v r
    else if v < x then
      .node l v (bstInsert x r)
    else
      .node l v r

/-- Teorema de Corrección 1: El elemento recién insertado `x` siempre pertenece a `bstInsert x t` -/
theorem mem_bstInsert_self (x : Nat) (t : Tree Nat) : mem x (bstInsert x t) := by
  induction t with
  | leaf =>
    simp
  | node l v r ihl ihr =>
    dsimp [bstInsert]
    split
    · -- Caso x < v:
      exact Or.inr (Or.inl ihl)
    · split
      · -- Caso v < x:
        exact Or.inr (Or.inr ihr)
      · -- Caso ¬(x < v) ∧ ¬(v < x), luego x = v:
        rename_i h1 h2
        have h_eq : x = v := by omega
        exact Or.inl h_eq

/-- Teorema de Corrección 2: Insertar `y` nunca pierde un elemento `x` que ya estaba en `t` -/
theorem mem_bstInsert_of_mem (x y : Nat) (t : Tree Nat) (h : mem x t) :
    mem x (bstInsert y t) := by
  induction t with
  | leaf =>
    nomatch h
  | node l v r ihl ihr =>
    dsimp [bstInsert]
    rcases h with rfl | hl | hr
    · split <;> try split
      all_goals exact Or.inl rfl
    · split
      · exact Or.inr (Or.inl (ihl hl))
      · split <;> exact Or.inr (Or.inl hl)
    · split
      · exact Or.inr (Or.inr hr)
      · split
        · exact Or.inr (Or.inr (ihr hr))
        · exact Or.inr (Or.inr hr)

end Tree
end LeanTT.M17
