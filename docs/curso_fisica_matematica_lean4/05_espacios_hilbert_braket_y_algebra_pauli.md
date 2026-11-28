# Lección 05: Espacios de Hilbert Cuánticos ($\mathbb{Z}[i]$), Bra-Ket, Observables Hermíticos y Álgebra de Pauli-Clifford

> **Módulos ejecutables asociados:** [`LeanTT/M76_QuantumHilbertSpacesAndBraKet.lean`](../../LeanTT/M76_QuantumHilbertSpacesAndBraKet.lean) y [`LeanTT/M77_PauliCliffordAlgebraAndUnitarity.lean`](../../LeanTT/M77_PauliCliffordAlgebraAndUnitarity.lean).
> **Navegación:** [⬅ Lección 04: Relatividad Especial](04_relatividad_especial_minkowski_y_lorentz.md) | [Siguiente: Bell, Teleportación y Gottesman-Knill ➡](06_entrelazamiento_bell_teleportacion_y_compilador_cuantico.md)

---

## 1. Postulados de Dirac-von Neumann sobre Enteros de Gauss $\mathbb{Z}[i]$

La Mecánica Cuántica sustituye el espacio de fases real $(q, p)$ por un **espacio de Hilbert complejo** $\mathcal{H}$:
1. **Estados puros ($\lvert\psi\rangle$):** vectores no nulos módulo fase/escala global en $\mathcal{H}$. Para un qubit, $\mathcal{H}_2 \cong \mathbb{C}^2$ con base computacional $\lvert 0\rangle = (1, 0)^T$ y $\lvert 1\rangle = (0, 1)^T$.
2. **Producto interno Bra-Ket ($\langle\psi\mid\phi\rangle$):** forma sesquilineal conjugada $\psi_0^* \phi_0 + \psi_1^* \phi_1$, que define la probabilidad de transición de **Born** proporcional a $|\langle\psi\mid\phi\rangle|^2 \ge 0$.
3. **Observables físicos ($A = A^\dagger$):** operadores lineales autoadjuntos (hermíticos), cuyos valores medibles y valores esperados $\langle\psi\mid A\psi\rangle$ son **estrictamente números reales**.
4. **Evolución cerrada ($U^\dagger U = I$):** transformaciones unitarias reversibles que conservan la norma y la ortogonalidad de estados.

```lean
namespace CursoFisica.L05

/-- Enteros de Gauss z = re + i·im para aritmética cuántica exacta en el kernel: -/
structure Cplx where
  re : Int
  im : Int
  deriving Repr, DecidableEq

def Cplx.zero  : Cplx := ⟨0, 0⟩
def Cplx.one   : Cplx := ⟨1, 0⟩
def Cplx.iUnit : Cplx := ⟨0, 1⟩
def Cplx.conj (z : Cplx) : Cplx := ⟨z.re, -z.im⟩
def Cplx.add (z w : Cplx) : Cplx := ⟨z.re + w.re, z.im + w.im⟩
def Cplx.mul (z w : Cplx) : Cplx := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩
def Cplx.normSq (z : Cplx) : Int := z.re * z.re + z.im * z.im

structure Ket2 where
  c0 : Cplx
  c1 : Cplx
  deriving Repr, DecidableEq

def braket (ψ φ : Ket2) : Cplx :=
  Cplx.add (Cplx.mul (Cplx.conj ψ.c0) φ.c0) (Cplx.mul (Cplx.conj ψ.c1) φ.c1)

/-- Simetría conjugada de Dirac: ⟨ψ | φ⟩ = ⟨φ | ψ⟩* -/
theorem braket_conj_symm (ψ φ : Ket2) : braket ψ φ = Cplx.conj (braket φ ψ) := by
  cases ψ with | mk x0 x1 =>
  cases φ with | mk y0 y1 =>
  cases x0; cases x1; cases y0; cases y1
  dsimp [braket, Cplx.add, Cplx.mul, Cplx.conj]
  simp only [Cplx.mk.injEq, Int.neg_mul]
  constructor
  · rename_i xr xi yr yi xr2 xi2 yr2 yi2
    rw [Int.mul_comm xr2 xr, Int.mul_comm xi2 xi, Int.mul_comm yr2 yr, Int.mul_comm yi2 yi]
  · rename_i xr xi yr yi xr2 xi2 yr2 yi2
    rw [Int.mul_comm xr2 xi, Int.mul_comm xi2 xr, Int.mul_comm yr2 yi, Int.mul_comm yi2 yr]
    omega

end CursoFisica.L05
```

---

## 2. El Álgebra de Espín-1/2 de Pauli y las Puertas del Grupo de Clifford

Las tres matrices de Pauli ($X, Y, Z$) son simultáneamente **hermíticas** ($P^\dagger = P$, observables de espín en los ejes $x, y, z$) y **unitarias involutivas** ($P^2 = I$, puertas lógicas cuánticas):
$$X = \begin{pmatrix} 0 & 1 \\ 1 & 0 \end{pmatrix}, \qquad Y = \begin{pmatrix} 0 & -i \\ i & 0 \end{pmatrix}, \qquad Z = \begin{pmatrix} 1 & 0 \\ 0 & -1 \end{pmatrix}.$$

Junto con la puerta de **Hadamard escalada** $\tilde{H} = \sqrt{2} H = \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}$ y la puerta de fase $S = \begin{pmatrix} 1 & 0 \\ 0 & i \end{pmatrix}$, generan el **Grupo de Clifford de 1 Qubit**, que conjuga elementos de Pauli en elementos de Pauli:

```lean
open CursoFisica.L05

structure Mat2C where
  m00 : Cplx
  m01 : Cplx
  m10 : Cplx
  m11 : Cplx
  deriving Repr, DecidableEq

def matMul (A B : Mat2C) : Mat2C :=
  { m00 := Cplx.add (Cplx.mul A.m00 B.m00) (Cplx.mul A.m01 B.m10)
  , m01 := Cplx.add (Cplx.mul A.m00 B.m01) (Cplx.mul A.m01 B.m11)
  , m10 := Cplx.add (Cplx.mul A.m10 B.m00) (Cplx.mul A.m11 B.m10)
  , m11 := Cplx.add (Cplx.mul A.m10 B.m01) (Cplx.mul A.m11 B.m11) }

def matScale (c : Cplx) (A : Mat2C) : Mat2C :=
  ⟨Cplx.mul c A.m00, Cplx.mul c A.m01, Cplx.mul c A.m10, Cplx.mul c A.m11⟩

def matId : Mat2C := ⟨Cplx.one, Cplx.zero, Cplx.zero, Cplx.one⟩
def pauliX : Mat2C := ⟨⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩⟩
def pauliY : Mat2C := ⟨⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩⟩
def pauliZ : Mat2C := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩⟩
def hadamard2 : Mat2C := ⟨⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩⟩
def phaseS    : Mat2C := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩⟩
def phaseSdg  : Mat2C := ⟨⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩⟩

/-- Verificación automática en el kernel de XY = iZ, HXH = Z (×2) y SXS† = Y: -/
theorem identidades_pauli_clifford :
    matMul pauliX pauliY = matScale Cplx.iUnit pauliZ ∧
    matMul (matMul hadamard2 pauliX) hadamard2 = matScale ⟨2, 0⟩ pauliZ ∧
    matMul (matMul phaseS pauliX) phaseSdg = pauliY := by
  decide

#eval matMul hadamard2 hadamard2 -- 2 · I
```

---

👉 **Siguiente lección:** [**Lección 06 — Entrelazamiento de Bell, No-Clonación, Teleportación Cuántica y Proyecto Cumbre V (Gottesman-Knill)**](06_entrelazamiento_bell_teleportacion_y_compilador_cuantico.md)
