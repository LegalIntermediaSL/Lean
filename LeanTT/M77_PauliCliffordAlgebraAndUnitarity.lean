import LeanTT.M76_QuantumHilbertSpacesAndBraKet

/-!
# Módulo 77: Álgebra de Pauli $\mathfrak{su}(2)$, Grupo de Clifford y Preservación Unitaria de la Norma
Construimos sobre `LeanTT.M76` el álgebra matricial exacta de operadores de 1 qubit (`Mat2C`)
para demostrar las identidades estructurales de la computación cuántica y la física del espín-1/2:

1. **Matrices de Pauli ($I, X, Y, Z$)** y puertas del **Grupo de Clifford ($\sqrt{2} H, S, S^\dagger$)**:
   - Hermiticidad e involutividad exacta: $X^2 = Y^2 = Z^2 = I$, $(\sqrt{2} H)^2 = 2I$.
   - Álgebra cuaterniónica de espín: $X Y = i Z$, $Y Z = i X$, $Z X = i Y$.
   - Relaciones de anticonmutación de Clifford: $\{X, Y\} = \{Y, Z\} = \{Z, X\} = 0$.
2. **Cambio de Base de Clifford por Conjugación:**
   - Hadamard intercambia las bases $X$ y $Z$: $(\sqrt{2}H) X (\sqrt{2}H) = 2 Z$ y
     $(\sqrt{2}H) Z (\sqrt{2}H) = 2 X$.
   - La puerta de fase $S = \text{diag}(1, i)$ rota $X$ hacia $Y$: $S X S^\dagger = Y$.
3. **Teorema de Evolución Unitaria (`scaledUnitary_preserves_norm`):** toda transformación unitaria
   escalada ($U^\dagger U = s \cdot I$) preserva la norma de cualquier estado cuántico simbólico
   $\langle U\psi \mid U\psi \rangle = s \cdot \langle \psi \mid \psi \rangle$ (conservación de la
   probabilidad total de Born!).
-/

namespace LeanTT.M77

open LeanTT.M76

/-- Suma, matriz nula, escalado y multiplicación de matrices complejas $2 \times 2$ (`Mat2C`): -/
def matZero : Mat2C := ⟨Cplx.zero, Cplx.zero, Cplx.zero, Cplx.zero⟩
def matId   : Mat2C := ⟨Cplx.one,  Cplx.zero, Cplx.zero, Cplx.one⟩

def matAdd (A B : Mat2C) : Mat2C :=
  { m00 := Cplx.add A.m00 B.m00
  , m01 := Cplx.add A.m01 B.m01
  , m10 := Cplx.add A.m10 B.m10
  , m11 := Cplx.add A.m11 B.m11 }

def matScale (c : Cplx) (A : Mat2C) : Mat2C :=
  { m00 := Cplx.mul c A.m00
  , m01 := Cplx.mul c A.m01
  , m10 := Cplx.mul c A.m10
  , m11 := Cplx.mul c A.m11 }

def matMul (A B : Mat2C) : Mat2C :=
  { m00 := Cplx.add (Cplx.mul A.m00 B.m00) (Cplx.mul A.m01 B.m10)
  , m01 := Cplx.add (Cplx.mul A.m00 B.m01) (Cplx.mul A.m01 B.m11)
  , m10 := Cplx.add (Cplx.mul A.m10 B.m00) (Cplx.mul A.m11 B.m10)
  , m11 := Cplx.add (Cplx.mul A.m10 B.m01) (Cplx.mul A.m11 B.m11) }

/-- Anticonmutador $\{A, B\} = A B + B A$ -/
def antiComm (A B : Mat2C) : Mat2C :=
  matAdd (matMul A B) (matMul B A)

/-! ## 1. Operadores de Pauli ($X, Y, Z$) y Puertas de Clifford ($\sqrt{2}H, S, S^\dagger$) -/

def pauliX : Mat2C := ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩
def pauliY : Mat2C := ⟨⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩
def pauliZ : Mat2C := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩⟩

/-- Puerta de Hadamard escalada por $\sqrt{2}$: $\tilde{H} = \sqrt{2} H = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ -/
def hadamardScaled : Mat2C := ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩

/-- Puerta de fase $S = \text{diag}(1, i)$ y su adjunta $S^\dagger = \text{diag}(1, -i)$ -/
def phaseS   : Mat2C := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩⟩
def phaseSdg : Mat2C := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩⟩

/-! ## 2. Teoremas Algebraicos del Grupo de Pauli y Clifford -/

theorem pauli_hermitian_and_involutive :
    IsHermitian pauliX ∧ IsHermitian pauliY ∧ IsHermitian pauliZ ∧
    matMul pauliX pauliX = matId ∧
    matMul pauliY pauliY = matId ∧
    matMul pauliZ pauliZ = matId := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- Multiplicación cíclica de espín-1/2: $X Y = i Z$, $Y Z = i X$, $Z X = i Y$ -/
theorem pauli_cyclic_products :
    matMul pauliX pauliY = matScale Cplx.iUnit pauliZ ∧
    matMul pauliY pauliZ = matScale Cplx.iUnit pauliX ∧
    matMul pauliZ pauliX = matScale Cplx.iUnit pauliY := by
  decide

/-- Álgebra de Clifford $Cl_{3,0}(\mathbb{R})$: las tres matrices de Pauli anticonmutan dos a dos! -/
theorem pauli_anticommutation :
    antiComm pauliX pauliY = matZero ∧
    antiComm pauliY pauliZ = matZero ∧
    antiComm pauliZ pauliX = matZero := by
  decide

/-- Involutividad escalada de Hadamard ($\tilde{H}^2 = 2 I$) y unitariedad de $S$ ($S^\dagger S = I$, $S^2 = Z$): -/
theorem clifford_fundamental_relations :
    matMul hadamardScaled hadamardScaled = matScale ⟨2, 0⟩ matId ∧
    matMul phaseSdg phaseS = matId ∧
    matMul phaseS phaseS = pauliZ := by
  decide

/-- **NORMALIZACIÓN DEL GRUPO DE PAULI POR EL GRUPO DE CLIFFORD:**
    - Conjugar $X$ por Hadamard produce $Z$ ($\tilde{H} X \tilde{H} = 2 Z$, es decir, $H X H = Z$!).
    - Conjugar $Z$ por Hadamard produce $X$ ($\tilde{H} Z \tilde{H} = 2 X$, es decir, $H Z H = X$!).
    - Conjugar $X$ por la puerta de fase $S$ produce $Y$ ($S X S^\dagger = Y$!). -/
theorem clifford_conjugation_identities :
    matMul (matMul hadamardScaled pauliX) hadamardScaled = matScale ⟨2, 0⟩ pauliZ ∧
    matMul (matMul hadamardScaled pauliZ) hadamardScaled = matScale ⟨2, 0⟩ pauliX ∧
    matMul (matMul phaseS pauliX) phaseSdg = pauliY := by
  decide

/-! ## 3. Asociatividad Acción Matriz-Ket y Conservación Unitaria de la Probabilidad -/

/-- Asociatividad de la acción matricial sobre estados cuánticos: $(A B)\lvert\psi\rangle = A(B\lvert\psi\rangle)$ -/
theorem applyMat2_mul (A B : Mat2C) (ψ : Ket2) :
    applyMat2 (matMul A B) ψ = applyMat2 A (applyMat2 B ψ) := by
  dsimp [applyMat2, matMul]
  simp only [Ket2.mk.injEq, Cplx.add_mul, Cplx.mul_add, Cplx.mul_assoc, Cplx.add_assoc]
  constructor
  · rw [Cplx.add_left_comm (Cplx.mul A.m01 (Cplx.mul B.m10 ψ.c0))]
  · rw [Cplx.add_left_comm (Cplx.mul A.m11 (Cplx.mul B.m10 ψ.c0))]

theorem applyMat2_scale_id (s : Int) (ψ : Ket2) :
    applyMat2 (matScale ⟨s, 0⟩ matId) ψ = ⟨Cplx.mul ⟨s, 0⟩ ψ.c0, Cplx.mul ⟨s, 0⟩ ψ.c1⟩ := by
  cases ψ with | mk x0 x1 =>
  cases x0; cases x1
  dsimp [applyMat2, matScale, matId, Cplx.one, Cplx.zero, Cplx.add, Cplx.mul]
  simp only [Int.mul_one, Int.mul_zero, Int.zero_mul, Int.sub_zero, Int.add_zero, Int.zero_add]

/-- **TEOREMA DE CONSERVACIÓN UNITARIA DEL PRODUCTO INTERNO (`scaledUnitary_preserves_braket`):**
    Si un operador $U$ satisface $U^\dagger U = s \cdot I$ ($s = 1$ para unitarias puras como
    $X, Y, Z, S$, o $s = 2$ para $\sqrt{2}H$), entonces preserva todos los productos internos y
    ángulos cuánticos:
    $$\langle U\psi \mid U\phi \rangle = s \cdot \langle \psi \mid \phi \rangle.$$ -/
theorem scaledUnitary_preserves_braket {U : Mat2C} {s : Int}
    (hUnit : matMul (dagger2 U) U = matScale ⟨s, 0⟩ matId) (ψ φ : Ket2) :
    braket (applyMat2 U ψ) (applyMat2 U φ) = Cplx.mul ⟨s, 0⟩ (braket ψ φ) := by
  calc
    braket (applyMat2 U ψ) (applyMat2 U φ)
      = braket (applyMat2 (dagger2 U) (applyMat2 U ψ)) φ :=
          (braket_dagger_left U (applyMat2 U ψ) φ).symm
    _ = braket (applyMat2 (matMul (dagger2 U) U) ψ) φ := by
          rw [← applyMat2_mul]
    _ = braket (applyMat2 (matScale ⟨s, 0⟩ matId) ψ) φ := by
          rw [hUnit]
    _ = Cplx.mul ⟨s, 0⟩ (braket ψ φ) := by
          rw [applyMat2_scale_id]
          dsimp [braket]
          have hConjReal : Cplx.conj ⟨s, 0⟩ = ⟨s, 0⟩ := rfl
          rw [Cplx.conj_mul, Cplx.conj_mul, hConjReal, Cplx.mul_assoc, Cplx.mul_assoc, ← Cplx.mul_add]

-- Acción ejecutable: H|0⟩ = |+⟩ y H|+⟩ = 2|0⟩ (interferencia constructiva y destructiva exacta!)
#eval applyMat2 hadamardScaled ket0
#eval applyMat2 hadamardScaled ketPlus

end LeanTT.M77
