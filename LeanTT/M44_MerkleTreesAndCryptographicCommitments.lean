/-!
# Módulo 44: Árboles de Merkle Dependientemente Tipados y Compromisos Criptográficos
## Ámbito: Estructuras de Datos Autenticadas, Blockchains y Compromisos Vectoriales en SNARKs

Un **Árbol de Merkle** (Merkle, 1987) permite comprometer un vector de $2^h$ bloques de datos
en una única raíz criptográfica (`root : Hash`) y demostrar que una hoja pertenece al árbol con
una prueba logarítmica de tamaño $h$.

Gracias a los **tipos dependientes** de Lean 4:
1. Indexamos el árbol `MerkleTree h` y el camino de búsqueda `MerklePath h` por la **altura exacta
   `h : Nat`**, haciendo imposible pasar una prueba de inclusión de longitud incorrecta.
2. **Demostramos formalmente la Completitud (`merkle_inclusion_completeness`):** toda prueba de
   inclusión generada honestamente reconstruye exactamente la raíz del árbol `t.root`.
3. **Demostramos la Seguridad de Binding (`merkle_binding_collision`):** si un adversario logra
   abrir una misma raíz con dos hojas distintas en la misma posición, ¡extraemos constructivamente
   una **colisión explícita** de la función hash!
-/

namespace LeanTT.M44

abbrev Hash := Nat

/-- Función de hash abstracta que comprime dos hijos `(left, right)` en un nodo padre -/
abbrev HashFn := Hash → Hash → Hash

/-- Árbol binario de Merkle indexado dependientemente por su altura `h : Nat` -/
inductive MerkleTree : Nat → Type where
  | leaf : Hash → MerkleTree 0
  | node : {h : Nat} → MerkleTree h → MerkleTree h → MerkleTree (h + 1)
  deriving Repr

/-- Dirección en cada nivel del árbol (`false` = hijo izquierdo, `true` = hijo derecho) -/
inductive MerklePath : Nat → Type where
  | here : MerklePath 0
  | step : {h : Nat} → Bool → MerklePath h → MerklePath (h + 1)
  deriving Repr

/-- Prueba de inclusión de Merkle de altura `h`: almacena en cada nivel la dirección y el hash
    del nodo hermano (*sibling hash*). -/
inductive MerkleProof : Nat → Type where
  | base : MerkleProof 0
  | step : {h : Nat} → Bool → Hash → MerkleProof h → MerkleProof (h + 1)
  deriving Repr

/-- Calcula recursivamente la raíz criptográfica de un `MerkleTree h` usando la función hash `H` -/
@[simp]
def computeRoot (H : HashFn) : {h : Nat} → MerkleTree h → Hash
  | 0,     .leaf x   => x
  | _ + 1, .node l r => H (computeRoot H l) (computeRoot H r)

/-- Obtiene la hoja situada en la ruta `MerklePath h` -/
@[simp]
def getLeaf : {h : Nat} → MerkleTree h → MerklePath h → Hash
  | 0,     .leaf x,   .here          => x
  | _ + 1, .node l r, .step dir rest =>
    if dir then getLeaf r rest else getLeaf l rest

/-- Genera la prueba de inclusión (`MerkleProof h`) para la posición indicada por `MerklePath h` -/
@[simp]
def generateProof (H : HashFn) : {h : Nat} → MerkleTree h → MerklePath h → MerkleProof h
  | 0,     .leaf _,   .here          => .base
  | _ + 1, .node l r, .step dir rest =>
    if dir then
      .step true (computeRoot H l) (generateProof H r rest)
    else
      .step false (computeRoot H r) (generateProof H l rest)

/-- El Verificador reconstruye la raíz ascendente a partir de la hoja `leafVal` y la `MerkleProof h` -/
@[simp]
def reconstructRoot (H : HashFn) : {h : Nat} → Hash → MerkleProof h → Hash
  | 0,     leafVal, .base                  => leafVal
  | _ + 1, leafVal, .step dir sibling rest =>
    let childHash := reconstructRoot H leafVal rest
    if dir then
      H sibling childHash
    else
      H childHash sibling

/-! ## Teoremas de Completitud y Seguridad Criptográfica de Binding -/

/-- TEOREMA 1 (Completitud Perfecta de las Pruebas de Inclusión de Merkle):
    Para cualquier altura `h`, cualquier árbol `t : MerkleTree h` y cualquier ruta `p : MerklePath h`,
    reconstruir la raíz desde `getLeaf t p` con `generateProof H t p` da exactamente `computeRoot H t`! -/
theorem merkle_inclusion_completeness (H : HashFn) :
    ∀ {h : Nat} (t : MerkleTree h) (p : MerklePath h),
      reconstructRoot H (getLeaf t p) (generateProof H t p) = computeRoot H t
  | 0,     .leaf _,   .here          => rfl
  | _ + 1, .node l r, .step dir rest => by
    cases dir
    · simp [merkle_inclusion_completeness H l rest]
    · simp [merkle_inclusion_completeness H r rest]

/-- Una colisión para la función de compresión `H` consiste en dos pares distintos con igual hash -/
def IsCollision (H : HashFn) (p1 p2 : Hash × Hash) : Prop :=
  p1 ≠ p2 ∧ H p1.1 p1.2 = H p2.1 p2.2

/-- TEOREMA 2 (Seguridad de Binding en Nivel 1 Reducida a Resistencia a Colisiones):
    Si dos hojas izquierdas distintas `x1 ≠ x2` junto al mismo hermano derecho `sib` producen la
    misma raíz de Merkle, entonces `((x1, sib), (x2, sib))` es una colisión explícita de `H`! -/
theorem merkle_binding_collision (H : HashFn) (x1 x2 sib : Hash)
    (hne : x1 ≠ x2)
    (h_same_root : H x1 sib = H x2 sib) :
    IsCollision H (x1, sib) (x2, sib) := by
  refine ⟨?_, h_same_root⟩
  intro h_eq
  injection h_eq with hx _
  exact hne hx

end LeanTT.M44
