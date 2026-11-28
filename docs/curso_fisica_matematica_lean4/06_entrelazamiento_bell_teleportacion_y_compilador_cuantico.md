# Lección 06: Entrelazamiento de Bell, No-Clonación, Teleportación Cuántica y Proyecto Cumbre V (Gottesman-Knill)

> **Módulos ejecutables asociados:** [`LeanTT/M78_QuantumEntanglementAndBellStates.lean`](../../LeanTT/M78_QuantumEntanglementAndBellStates.lean), [`LeanTT/M79_NoCloningTeleportationAndDeutschJozsa.lean`](../../LeanTT/M79_NoCloningTeleportationAndDeutschJozsa.lean) y [**`LeanTT/M80_VerifiedQuantumCircuitCompilerAndStabilizers.lean` (Proyecto Cumbre V)**](../../LeanTT/M80_VerifiedQuantumCircuitCompilerAndStabilizers.lean).
> **Navegación:** [⬅ Lección 05: Hilbert y Pauli-Clifford](05_espacios_hilbert_braket_y_algebra_pauli.md) | [🎓 Volver al Índice del Mini-Curso IV](00_indice_minicurso_fisica_lean4.md)

---

## 1. Demostración Formal del Entrelazamiento Cuántico en Estados de Bell (`M78`)

¿Cómo se demuestra matemáticamente que el par EPR $\lvert\Phi^+\rangle = \lvert 00\rangle + \lvert 11\rangle$ está **entrelazado** (es decir, que no puede escribirse como $\lvert u\rangle \otimes \lvert v\rangle$)?

Mediante el **Determinante de Segre-Schmidt** $\Delta(\Psi) = c_{00} c_{11} - c_{01} c_{10}$:
* Para cualquier estado producto $\lvert u\rangle \otimes \lvert v\rangle = (u_0 v_0, u_0 v_1, u_1 v_0, u_1 v_1)$, la conmutatividad de los escalares garantiza que $(u_0 v_0)(u_1 v_1) - (u_0 v_1)(u_1 v_0) = 0$.
* En cambio, para $\lvert\Phi^+\rangle = (1, 0, 0, 1)$, tenemos $\Delta(\lvert\Phi^+\rangle) = 1\cdot 1 - 0\cdot 0 = 1 \neq 0$.

Veamos la demostración constructiva completa en Lean 4:

```lean
namespace CursoFisica.L06

structure Ket2R where
  c0 : Int
  c1 : Int
  deriving Repr, DecidableEq

structure Ket4R where
  c00 : Int
  c01 : Int
  c10 : Int
  c11 : Int
  deriving Repr, DecidableEq

def tensorKet (u v : Ket2R) : Ket4R :=
  ⟨u.c0 * v.c0, u.c0 * v.c1, u.c1 * v.c0, u.c1 * v.c1⟩

def bellPhiPlus : Ket4R := ⟨1, 0, 0, 1⟩

def schmidtDet (Ψ : Ket4R) : Int :=
  Ψ.c00 * Ψ.c11 - Ψ.c01 * Ψ.c10

theorem det_tensor_zero (u v : Ket2R) : schmidtDet (tensorKet u v) = 0 := by
  dsimp [schmidtDet, tensorKet]
  rw [Int.mul_assoc u.c0 v.c0 (u.c1 * v.c1), ← Int.mul_assoc v.c0 u.c1 v.c1,
      Int.mul_comm v.c0 u.c1, Int.mul_assoc u.c1 v.c0 v.c1,
      ← Int.mul_assoc u.c0 u.c1 (v.c0 * v.c1)]
  rw [Int.mul_assoc u.c0 v.c1 (u.c1 * v.c0), ← Int.mul_assoc v.c1 u.c1 v.c0,
      Int.mul_comm v.c1 u.c1, Int.mul_assoc u.c1 v.c1 v.c0,
      Int.mul_comm v.c1 v.c0, ← Int.mul_assoc u.c0 u.c1 (v.c0 * v.c1)]
  omega

/-- TEOREMA DE ENTRELAZAMIENTO: No existen `u, v` tales que `u ⊗ v = |Φ⁺⟩`! -/
theorem bellPhiPlus_inseparable : ¬ (∃ u v : Ket2R, tensorKet u v = bellPhiPlus) := by
  rintro ⟨u, v, hEq⟩
  have h0 := det_tensor_zero u v
  rw [hEq] at h0
  dsimp [schmidtDet, bellPhiPlus] at h0
  omega

end CursoFisica.L06
```
*(En [`LeanTT/M78_QuantumEntanglementAndBellStates.lean`](../../LeanTT/M78_QuantumEntanglementAndBellStates.lean) esta misma demostración está verificada sobre amplitudes complejas completas en $\mathbb{Z}[i]$ para los 4 estados de la base de Bell).*

---

## 2. Protocolo de Teleportación Cuántica de 3 Qubits Verificado Extremo a Extremo (`M79`)

Dado que el **Teorema de No-Clonación** (Wootters & Zurek, 1982 — demostrado en [`M79`](../../LeanTT/M79_NoCloningTeleportationAndDeutschJozsa.lean)) prohíbe copiar un estado cuántico desconocido $\lvert\psi\rangle = \alpha\lvert 0\rangle + \beta\lvert 1\rangle$, ¿cómo puede Alice transmitir $\lvert\psi\rangle$ a Bob enviando únicamente **2 bits clásicos** $(m_1, m_2)$?

Consumiendo un par entrelazado $\lvert\Phi^+\rangle_{BC}$ previamente compartido:
1. Estado inicial de 3 qubits: $\lvert\psi\rangle_A \otimes \lvert\Phi^+\rangle_{BC}$.
2. Alice entrelaza $A$ con $B$ mediante $\text{CNOT}_{AB}$ y aplica Hadamard $H_A$.
3. Alice mide $(A, B) \to (m_1, m_2) \in \{0, 1\}^2$ (destruyendo su copia local, respetando así la No-Clonación!) y envía $(m_1, m_2)$ a Bob.
4. Bob aplica $Z^{m_1} X^{m_2}$ sobre su qubit $C$ y recupera **exactamente** $\lvert\psi\rangle$ en las 4 ramas posibles:

```lean
open CursoFisica.L06

structure Ket8R where
  a000 : Int
  a001 : Int
  a010 : Int
  a011 : Int
  a100 : Int
  a101 : Int
  a110 : Int
  a111 : Int

def teleportBranch (ψ : Ket2R) (m1 m2 : Bool) : Ket2R :=
  -- 1. |ψ⟩_A ⊗ |Φ⁺⟩_BC seguido de CNOT_AB y H_A:
  let s : Ket8R :=
    { a000 := ψ.c0,  a001 := ψ.c1
    , a010 := ψ.c1,  a011 := ψ.c0
    , a100 := ψ.c0,  a101 := -ψ.c1
    , a110 := -ψ.c1, a111 := ψ.c0 }
  -- 2. Colapso de medida (m1, m2) en Alice:
  let bobRaw : Ket2R :=
    match m1, m2 with
    | false, false => ⟨s.a000, s.a001⟩
    | false, true  => ⟨s.a010, s.a011⟩
    | true,  false => ⟨s.a100, s.a101⟩
    | true,  true  => ⟨s.a110, s.a111⟩
  -- 3. Corrección condicional de Pauli Z^m1 X^m2 en Bob:
  let afterX : Ket2R := if m2 then ⟨bobRaw.c1, bobRaw.c0⟩ else bobRaw
  if m1 then ⟨afterX.c0, -afterX.c1⟩ else afterX

/-- En las 4 ramas de medida posibles, Bob obtiene idénticamente el qubit original `ψ`! -/
theorem teleport_always_succeeds (ψ : Ket2R) (m1 m2 : Bool) :
    teleportBranch ψ m1 m2 = ψ := by
  cases ψ with | mk α β =>
  cases m1 <;> cases m2 <;> simp [teleportBranch, Int.neg_neg]

#eval teleportBranch ⟨7, -11⟩ true true -- { c0 := 7, c1 := -11 }
```

---

## 3. Proyecto Cumbre V (`M80`): Optimizador de Circuitos y Simulador de Gottesman-Knill

En [**`LeanTT/M80_VerifiedQuantumCircuitCompilerAndStabilizers.lean`**](../../LeanTT/M80_VerifiedQuantumCircuitCompilerAndStabilizers.lean) cerramos el curso construyendo dos pilares de la ingeniería cuántica verificada:

1. **Compilador Optimizador Peephole (`optimize1`):** reduce la profundidad de circuitos cancelando involuciones ($XX, YY, ZZ \to I$), inversos ($S S^\dagger \to I$) y fusionando puertas de fase ($S S \to Z$), certificado con `denoteCircuit1_optimize1` y `length_optimize1_le`.
2. **Actualizador Simbólico del Teorema de Gottesman-Knill (`conjugatePauliSymbolic`):** representa cada estabilizador de Pauli con signo $(\pm 1, \{I, X, Y, Z\})$ en 3 bits clásicos y actualiza $C P C^\dagger$ en tiempo $O(1)$:

```lean
namespace DemoGottesmanKnill

inductive PauliSym | I | X | Y | Z deriving Repr, DecidableEq
inductive CliffGen | H | S | X | Z deriving Repr, DecidableEq

structure SignedPauli where
  neg : Bool
  sym : PauliSym
  deriving Repr, DecidableEq

def stepGK (c : CliffGen) (sp : SignedPauli) : SignedPauli :=
  match c, sp.sym with
  | .H, .I => ⟨sp.neg, .I⟩  | .H, .X => ⟨sp.neg, .Z⟩
  | .H, .Y => ⟨!sp.neg, .Y⟩ | .H, .Z => ⟨sp.neg, .X⟩
  | .S, .I => ⟨sp.neg, .I⟩  | .S, .X => ⟨sp.neg, .Y⟩
  | .S, .Y => ⟨!sp.neg, .X⟩ | .S, .Z => ⟨sp.neg, .Z⟩
  | .X, .I => ⟨sp.neg, .I⟩  | .X, .X => ⟨sp.neg, .X⟩
  | .X, .Y => ⟨!sp.neg, .Y⟩ | .X, .Z => ⟨!sp.neg, .Z⟩
  | .Z, .I => ⟨sp.neg, .I⟩  | .Z, .X => ⟨!sp.neg, .X⟩
  | .Z, .Y => ⟨!sp.neg, .Y⟩ | .Z, .Z => ⟨sp.neg, .Z⟩

-- Propiedad grupal de orden 3 del elemento (H · S) sobre las direcciones de espín X → Y → Z → X (con signo):
#eval stepGK .H (stepGK .S ⟨false, .X⟩) -- -Y
#eval stepGK .S (stepGK .H ⟨false, .Z⟩) -- +Y

theorem double_hadamard_pauli_id (sp : SignedPauli) :
    stepGK .H (stepGK .H sp) = sp := by
  cases sp with | mk neg sym =>
  cases neg <;> cases sym <;> rfl

end DemoGottesmanKnill
```

---

## 🎓 ¿Cómo Continuar?

* Resuelve los 5 ejercicios prácticos guiados del [**Taller 06 (`E06_WorkoutPhysicsAndQuantumMechanics.lean`)**](../../LeanTT/Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean) y contrasta tus pruebas con el [**Solucionario Comentado `S06`**](../../LeanTT/Solutions/S06_WorkoutPhysicsAndQuantumMechanics.lean).
* Explora el proyecto abierto **[PhysLean (`HepLean`)](https://github.com/HEPLean/PhysLean)** en GitHub para ver cómo estas mismas ideas escalan en `Mathlib4` al grupo de Lorentz continuo $SO^+(1,3)$, tensores espinoriales de Weyl y teoría cuántica de campos gauge.
