/-!
# Módulo 18: Algoritmos de Ordenación Formalmente Verificados (`Insertion Sort`)
## Ámbito: Verificación Formal de Algoritmos

Demostrar que un algoritmo de ordenación es correcto exige probar dos propiedades:
1. Que la salida está **ordenada** (`Sorted (insertionSort xs)`).
2. Que preserva invariantes como la **longitud** (`(insertionSort xs).length = xs.length`).

En este módulo definimos inductivamente el predicado `Sorted` y demostramos formalmente
que `insertionSort` siempre devuelve una lista ordenada para cualquier entrada `xs : List Nat`.
-/

namespace LeanTT.M18

/-- Inserta un número `x` en la posición ordenada correspondiente de una lista -/
@[simp]
def orderedInsert (x : Nat) : List Nat → List Nat
  | []      => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: orderedInsert x ys

/-- Ordenación por inserción (`Insertion Sort`) -/
@[simp]
def insertionSort : List Nat → List Nat
  | []      => []
  | x :: xs => orderedInsert x (insertionSort xs)

#eval insertionSort [9, 3, 7, 1, 5, 2, 8] -- [1, 2, 3, 5, 7, 8, 9]

/-! ## 1. Preservación de la Longitud -/

@[simp]
theorem length_orderedInsert (x : Nat) (xs : List Nat) :
    (orderedInsert x xs).length = xs.length + 1 := by
  induction xs with
  | nil          => rfl
  | cons y ys ih =>
    dsimp [orderedInsert]
    split
    · rfl
    · simp [ih]

theorem length_insertionSort (xs : List Nat) :
    (insertionSort xs).length = xs.length := by
  induction xs with
  | nil          => rfl
  | cons x xs ih => simp [ih]

/-! ## 2. Especificación Inductiva de Lista Ordenada (`Sorted`) -/

/-- Una lista está ordenada si es vacía, tiene un solo elemento, o su cabeza es `≤` que
    el siguiente elemento y la cola está ordenada. -/
inductive Sorted : List Nat → Prop where
  | nil  : Sorted []
  | single (x : Nat) : Sorted [x]
  | cons (x y : Nat) (ys : List Nat) (hle : x ≤ y) (hs : Sorted (y :: ys)) :
      Sorted (x :: y :: ys)

/-- Lema clave: Si `y :: ys` está ordenada, entonces `orderedInsert x (y :: ys)` también lo está -/
theorem sorted_orderedInsert (x : Nat) (xs : List Nat) (h : Sorted xs) :
    Sorted (orderedInsert x xs) := by
  induction h with
  | nil =>
    exact Sorted.single x
  | single y =>
    dsimp [orderedInsert]
    split
    · next hxy => exact Sorted.cons x y [] hxy (Sorted.single y)
    · next hxy =>
      have hyx : y ≤ x := by omega
      exact Sorted.cons y x [] hyx (Sorted.single x)
  | cons y z zs hyz hsz ih =>
    dsimp [orderedInsert]
    split
    · next hxy =>
      exact Sorted.cons x y (z :: zs) hxy (Sorted.cons y z zs hyz hsz)
    · next hxy =>
      have hyx : y ≤ x := by omega
      dsimp [orderedInsert] at ih ⊢
      split
      · next hxz =>
        split at ih
        · exact Sorted.cons y x (z :: zs) hyx ih
        · contradiction
      · next hxz =>
        split at ih
        · contradiction
        · exact Sorted.cons y z (orderedInsert x zs) hyz ih

/-- TEOREMA PRINCIPAL: Para toda lista `xs : List Nat`, `insertionSort xs` está ordenada! -/
theorem sorted_insertionSort (xs : List Nat) : Sorted (insertionSort xs) := by
  induction xs with
  | nil          => exact Sorted.nil
  | cons x xs ih => exact sorted_orderedInsert x (insertionSort xs) ih

end LeanTT.M18
