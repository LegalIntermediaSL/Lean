/-!
# Módulo 66: Computación Reversible y Lógica de Puertas Cuánticas Discretas (Pauli-$X$, CNOT, SWAP, Toffoli y Fredkin)
## Ámbito: Circuitos Cuánticos Reversibles (Landauer / Bennett / Nielsen & Chuang) y Síntesis de Circuitos

Toda puerta cuántica unitaria $U$ que actúa como permutación sobre la base computacional
($|q_1, \dots, q_n\rangle \in \{0, 1\}^n$) es **estrictamente reversible** (biyectiva).
Más aún, las puertas fundamentales de la computación cuántica y reversible (**Pauli-$X$**,
**`CNOT`**, **`SWAP`**, **`Toffoli` / `CCNOT`** y **`Fredkin` / `CSWAP`**) son **autoinversas (involuciones)**:
$$U(U(s)) = s$$

En este módulo:
1. Formalizamos registros de 2 qubits (`Reg2`) y 3 qubits (`Reg3`) en la base computacional.
2. Definimos las puertas `cnot12`, `cnot21`, `swap2`, la puerta universal reversible de **Toffoli (`toffoli`)**
   y la puerta conservadora de peso de Hamming de **Fredkin (`fredkin`)**.
3. Demostramos la **Reversibilidad Involutiva** de `cnot12`, `toffoli` y `fredkin`.
4. Demostramos el célebre **Teorema de Síntesis Cuántica de `SWAP` mediante 3 Puertas `CNOT`**
   (`cnot12 (cnot21 (cnot12 s)) = swap2 s`) y la **Conservación del Peso de Hamming de Fredkin**.
-/

namespace LeanTT.M66

/-- Estado en la base computacional de un registro de 2 qubits `|q1, q2⟩` -/
structure Reg2 where
  q1 : Bool
  q2 : Bool
  deriving Repr, DecidableEq

/-- Estado en la base computacional de un registro de 3 qubits `|q1, q2, q3⟩` -/
structure Reg3 where
  q1 : Bool
  q2 : Bool
  q3 : Bool
  deriving Repr, DecidableEq

/-- Puerta `CNOT` con control en `q1` y objetivo en `q2`: `|q1, q2⟩ ↦ |q1, q1 ⊕ q2⟩` -/
@[simp]
def cnot12 (s : Reg2) : Reg2 :=
  { q1 := s.q1, q2 := xor s.q1 s.q2 }

/-- Puerta `CNOT` invertida con control en `q2` y objetivo en `q1`: `|q1, q2⟩ ↦ |q1 ⊕ q2, q2⟩` -/
@[simp]
def cnot21 (s : Reg2) : Reg2 :=
  { q1 := xor s.q1 s.q2, q2 := s.q2 }

/-- Puerta `SWAP` de 2 qubits: `|q1, q2⟩ ↦ |q2, q1⟩` -/
@[simp]
def swap2 (s : Reg2) : Reg2 :=
  { q1 := s.q2, q2 := s.q1 }

/-- Puerta Universal Reversible de **Toffoli (`CCNOT`)** sobre 3 qubits:
    invierte el tercer qubit `q3` si y solo si `q1` y `q2` son ambos `true`. -/
@[simp]
def toffoli (s : Reg3) : Reg3 :=
  { q1 := s.q1
  , q2 := s.q2
  , q3 := xor (s.q1 && s.q2) s.q3 }

/-- Puerta Reversible Conservativa de **Fredkin (`CSWAP`)** sobre 3 qubits:
    si el qubit de control `q1` es `true`, intercambia `q2` y `q3`; de lo contrario los deja intactos. -/
@[simp]
def fredkin (s : Reg3) : Reg3 :=
  if s.q1 then
    { q1 := s.q1, q2 := s.q3, q3 := s.q2 }
  else
    s

/-- Peso de Hamming (número de qubits en estado `|1⟩`) de un registro de 3 qubits -/
@[simp]
def hammingWeight3 (s : Reg3) : Nat :=
  (if s.q1 then 1 else 0) + (if s.q2 then 1 else 0) + (if s.q3 then 1 else 0)

/-! ## 1. Teoremas de Reversibilidad, Síntesis de Circuitos y Conservación -/

/-- TEOREMA 1 (Involutividad / Reversibilidad de `CNOT`): -/
@[simp]
theorem cnot12_involutive (s : Reg2) :
    cnot12 (cnot12 s) = s := by
  cases s with | mk q1 q2 =>
  cases q1 <;> cases q2 <;> rfl

/-- TEOREMA 2 (Síntesis Exacta de `SWAP` con 3 Puertas `CNOT` Alternadas):
    En arquitecturas superconductoras donde solo existen puertas `CNOT` entre qubits vecinos,
    tres puertas `CNOT` alternadas (`cnot12 ∘ cnot21 ∘ cnot12`) implementan exactamente `swap2`! -/
theorem three_cnots_eq_swap2 (s : Reg2) :
    cnot12 (cnot21 (cnot12 s)) = swap2 s := by
  cases s with | mk q1 q2 =>
  cases q1 <;> cases q2 <;> rfl

/-- TEOREMA 3 (Involutividad / Reversibilidad de la Puerta Universal de Toffoli): -/
@[simp]
theorem toffoli_involutive (s : Reg3) :
    toffoli (toffoli s) = s := by
  cases s with | mk q1 q2 q3 =>
  cases q1 <;> cases q2 <;> cases q3 <;> rfl

/-- TEOREMA 4 (Involutividad / Reversibilidad de la Puerta de Fredkin): -/
@[simp]
theorem fredkin_involutive (s : Reg3) :
    fredkin (fredkin s) = s := by
  cases s with | mk q1 q2 q3 =>
  cases q1 <;> cases q2 <;> cases q3 <;> rfl

/-- TEOREMA 5 (Conservación Exacta del Peso de Hamming por la Puerta de Fredkin):
    La puerta de Fredkin preserva siempre el número total de `1`s en el registro cuántico. -/
theorem fredkin_preserves_hammingWeight (s : Reg3) :
    hammingWeight3 (fredkin s) = hammingWeight3 s := by
  cases s with | mk q1 q2 q3 =>
  cases q1 <;> cases q2 <;> cases q3 <;> rfl

end LeanTT.M66
