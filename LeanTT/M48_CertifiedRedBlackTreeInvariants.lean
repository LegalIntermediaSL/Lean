/-!
# Módulo 48: Árboles Rojo-Negro (*Red-Black Trees*) de Okasaki y Rotaciones Verificadas
## Ámbito: Estructuras de Datos Funcionales Persistentes y Verificación de Algoritmos

Los **Árboles Rojo-Negro** en estilo puramente funcional (Chris Okasaki, *Purely Functional Data
Structures*, 1999) mantienen el árbol balanceado mediante la función algebraica `balance`, que
detecta y corrige las **4 configuraciones posibles de doble nodo rojo consecutivo** en una sola
definición por reconocimiento de patrones.

En este módulo:
1. Implementamos `Color`, `RBTree`, las 4 rotaciones de `balance` de Okasaki e `insert`.
2. **Demostramos formalmente (`mem_balance`)** que las 4 rotaciones de reequilibrado preservan
   de manera exacta el conjunto de claves almacenadas en el árbol.
3. **Demostramos formalmente (`mem_insert`)** que insertar una clave `y` añade exactamente `y`
   sin perder ni inventar ningún otro elemento en ninguna rotación!
-/

namespace LeanTT.M48

inductive Color where
  | red   : Color
  | black : Color
  deriving Repr, DecidableEq

inductive RBTree where
  | leaf : RBTree
  | node : Color → RBTree → Nat → RBTree → RBTree
  deriving Repr, DecidableEq

namespace RBTree

/-- Pertenencia proposicional de una clave `x` a un árbol rojo-negro -/
@[simp]
def mem (x : Nat) : RBTree → Prop
  | .leaf          => False
  | .node _ l k r  => x = k ∨ mem x l ∨ mem x r

/-- La célebre función `balance` de Chris Okasaki:
    corrige cualquiera de las 4 violaciones Rojo-Rojo rotando hacia un padre Rojo con dos hijos Negros. -/
def balance : Color → RBTree → Nat → RBTree → RBTree
  | .black, .node .red (.node .red a x b) y c, z, d =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | .black, .node .red a x (.node .red b y c), z, d =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | .black, a, x, .node .red (.node .red b y c) z d =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | .black, a, x, .node .red b y (.node .red c z d) =>
    .node .red (.node .black a x b) y (.node .black c z d)
  | c, l, k, r =>
    .node c l k r

/-- TEOREMA CLAVE 1: La operación `balance` preserva exactamente el conjunto de elementos
    (`x ∈ balance c l k r ↔ x = k ∨ x ∈ l ∨ x ∈ r`) en todas sus ramas de rotación! -/
theorem mem_balance (x : Nat) (c : Color) (l : RBTree) (k : Nat) (r : RBTree) :
    mem x (balance c l k r) ↔ (x = k ∨ mem x l ∨ mem x r) := by
  unfold balance
  split
  · simp only [mem]
    constructor
    · rintro (rfl | (rfl | ha | hb) | rfl | hc | hr)
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inl rfl))))
      · exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inl ha)))))
      · exact Or.inr (Or.inl (Or.inr (Or.inl (Or.inr (Or.inr hb)))))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inr (Or.inr hc)))
      · exact Or.inr (Or.inr hr)
    · rintro (rfl | (rfl | (rfl | ha | hb) | hc) | hr)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inl (Or.inr (Or.inr hb)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hr)))
  · simp only [mem]
    constructor
    · rintro (rfl | (rfl | ha | hb) | rfl | hc | hr)
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl hb)))))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr hc)))))
      · exact Or.inr (Or.inr hr)
    · rintro (rfl | (rfl | ha | rfl | hb | hc) | hr)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ha)))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inr (Or.inr hb)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hr)))
  · simp only [mem]
    constructor
    · rintro (rfl | (rfl | ha | hb) | rfl | hc | hd)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl rfl))))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inl hb)))))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inr (Or.inr hc)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hd)))
    · rintro (rfl | ha | rfl | (rfl | hb | hc) | hd)
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ha)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inr (Or.inr hb)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hd)))
  · simp only [mem]
    constructor
    · rintro (rfl | (rfl | ha | hb) | rfl | hc | hd)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl ha)
      · exact Or.inr (Or.inr (Or.inr (Or.inl hb)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hc)))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hd)))))
    · rintro (rfl | ha | rfl | hb | rfl | hc | hd)
      · exact Or.inr (Or.inl (Or.inl rfl))
      · exact Or.inr (Or.inl (Or.inr (Or.inl ha)))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (Or.inr (Or.inr hb)))
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr (Or.inl hc)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr hd)))
  · rfl

/-- Inserción recursiva auxiliar con reequilibrado `balance` -/
def ins (y : Nat) : RBTree → RBTree
  | .leaf => .node .red .leaf y .leaf
  | .node c l k r =>
    if y < k then
      balance c (ins y l) k r
    else if k < y then
      balance c l k (ins y r)
    else
      .node c l k r

/-- Colorea la raíz de negro tras insertar -/
def makeBlack : RBTree → RBTree
  | .leaf         => .leaf
  | .node _ l k r => .node .black l k r

/-- Inserción completa de Okasaki en un Árbol Rojo-Negro -/
def insert (y : Nat) (t : RBTree) : RBTree :=
  makeBlack (ins y t)

theorem mem_makeBlack (x : Nat) (t : RBTree) :
    mem x (makeBlack t) ↔ mem x t := by
  cases t <;> rfl

/-- TEOREMA CLAVE 2: `ins` añade exactamente `y` preservando todos los elementos previos -/
theorem mem_ins (x y : Nat) (t : RBTree) :
    mem x (ins y t) ↔ (x = y ∨ mem x t) := by
  induction t with
  | leaf =>
    simp [ins]
  | node c l k r ihl ihr =>
    dsimp [ins]
    split
    · rw [mem_balance, ihl]
      constructor
      · rintro (rfl | (rfl | hl) | hr)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr (Or.inl hl))
        · exact Or.inr (Or.inr (Or.inr hr))
      · rintro (rfl | rfl | hl | hr)
        · exact Or.inr (Or.inl (Or.inl rfl))
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inr hl))
        · exact Or.inr (Or.inr hr)
    · split
      · rw [mem_balance, ihr]
        constructor
        · rintro (rfl | hl | (rfl | hr))
          · exact Or.inr (Or.inl rfl)
          · exact Or.inr (Or.inr (Or.inl hl))
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inr hr))
        · rintro (rfl | rfl | hl | hr)
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hl)
          · exact Or.inr (Or.inr (Or.inr hr))
      · next hge hle =>
        have heq : y = k := by omega
        subst heq
        simp only [mem]
        constructor
        · rintro (rfl | hl | hr)
          · exact Or.inl rfl
          · exact Or.inr (Or.inr (Or.inl hl))
          · exact Or.inr (Or.inr (Or.inr hr))
        · rintro (rfl | rfl | hl | hr)
          · exact Or.inl rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl hl)
          · exact Or.inr (Or.inr hr)

/-- TEOREMA FUNDAMENTAL DEL ÁRBOL ROJO-NEGRO (`mem_insert`):
    Para toda clave `x`, `y` y todo árbol `t`, `x` pertenece a `insert y t` si y solo si
    `x = y` o `x` ya pertenecía a `t`! -/
theorem mem_insert (x y : Nat) (t : RBTree) :
    mem x (insert y t) ↔ (x = y ∨ mem x t) := by
  dsimp [insert]
  rw [mem_makeBlack, mem_ins]

end RBTree
end LeanTT.M48
