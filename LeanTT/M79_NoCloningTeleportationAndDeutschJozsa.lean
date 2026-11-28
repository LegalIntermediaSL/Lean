import LeanTT.M78_QuantumEntanglementAndBellStates

/-!
# Módulo 79: Teorema de No-Clonación, Protocolo de Teleportación Cuántica y Algoritmo de Deutsch
Reunimos tres de los resultados más célebres de la **Teoría de la Información Cuántica (QIT)**
con demostraciones 100% formales en el kernel de Lean 4 (`0 sorry`):

1. **Teorema de No-Clonación de Wootters-Zurek-Dieks (1982):**
   Demostramos algebraicamente que ninguna operación lineal unitaria puede clonar simultáneamente
   dos estados cuánticos $\lvert\psi\rangle, \lvert\phi\rangle$ salvo que su producto interno cumpla
   $\langle\psi\mid\phi\rangle^2 = \langle\psi\mid\phi\rangle$, lo que obliga a $\langle\psi\mid\phi\rangle \in \{0, 1\}$
   (estados idénticos u ortogonales: imposible clonar superposiciones arbitrarias!).
2. **Protocolo de Teleportación Cuántica de 3 Qubits (Bennett, Brassard, Crépeau, Jozsa, Peres, Wootters 1993):**
   Modelamos el espacio completo de 3 qubits $\mathcal{H}_2^{\otimes 3} \cong \mathbb{C}^8$, el canal
   EPR compartido $\lvert\Phi^+\rangle_{BC}$, la medición de Bell de Alice (`CNOT` + `H`) y la
   corrección de Pauli $X^{m_2} Z^{m_1}$ de Bob a partir de 2 bits clásicos $(m_1, m_2)$, demostrando
   simbólicamente que **para todo estado desconocido $\lvert\psi\rangle = \alpha\lvert 0\rangle + \beta\lvert 1\rangle$
   y en las 4 ramas de medida**, Bob recupera exactamente $\lvert\psi\rangle$!
3. **Algoritmo Cuántico de Deutsch (Paralelismo Cuántico + *Phase Kickback*):**
   Demostramos que una **única consulta** al oráculo de fase $U_f$ determina con certeza absoluta si
   un predicado oculto $f : \text{Bool} \to \text{Bool}$ es constante o balanceado!
-/

namespace LeanTT.M79

open LeanTT.M76
open LeanTT.M77
open LeanTT.M78

/-! ## 1. Teorema de No-Clonación Cuántica (Wootters & Zurek, 1982) -/

/-- Factorización del producto interno en el producto tensorial:
    $\langle u_1 \otimes u_2 \mid v_1 \otimes v_2 \rangle = \langle u_1 \mid v_1 \rangle \cdot \langle u_2 \mid v_2 \rangle$. -/
theorem braket4_tensorKet (u1 u2 v1 v2 : Ket2) :
    braket4 (tensorKet u1 u2) (tensorKet v1 v2) = Cplx.mul (braket u1 v1) (braket u2 v2) := by
  dsimp [braket4, tensorKet, braket]
  simp only [Cplx.conj_mul, Cplx.mul4_swap, Cplx.add_mul, Cplx.mul_add, Cplx.add_assoc]
  rw [Cplx.add_left_comm (Cplx.mul (Cplx.mul (Cplx.conj u1.c0) v1.c0) (Cplx.mul (Cplx.conj u2.c1) v2.c1))]

/-- Idempotentes en el dominio de integridad $\mathbb{Z}[i]$: si $z^2 = z$, entonces $z = 0$ o $z = 1$! -/
theorem cplx_idempotent_zero_or_one (z : Cplx) (hIdem : Cplx.mul z z = z) :
    z = Cplx.zero ∨ z = Cplx.one := by
  have hDiffZero : Cplx.mul z (Cplx.sub z Cplx.one) = Cplx.zero := by
    cases z with | mk a b =>
    injection hIdem with hRe hIm
    dsimp [Cplx.mul, Cplx.sub, Cplx.one, Cplx.zero] at *
    simp only [Cplx.mk.injEq, Int.mul_sub, Int.mul_one, Int.sub_zero]
    exact ⟨by omega, by omega⟩
  have hNormProd : Cplx.normSq z * Cplx.normSq (Cplx.sub z Cplx.one) = 0 := by
    rw [← Cplx.normSq_mul, hDiffZero]
    rfl
  rcases Int.mul_eq_zero.mp hNormProd with hz0 | hz1
  · left
    exact (Cplx.normSq_eq_zero_iff z).mp hz0
  · right
    have hSubZero := (Cplx.normSq_eq_zero_iff (Cplx.sub z Cplx.one)).mp hz1
    cases z; dsimp [Cplx.sub, Cplx.one, Cplx.zero] at hSubZero
    injection hSubZero with h1 h2
    dsimp [Cplx.one]; simp only [Cplx.mk.injEq]; exact ⟨by omega, by omega⟩

/-- **TEOREMA DE NO-CLONACIÓN CUÁNTICA (`no_cloning_theorem`):**
    Supongamos que un operador isométrico/unitario $U$ en $\mathcal{H}_2 \otimes \mathcal{H}_2$
    (que preserva productos internos: $\langle U\Psi \mid U\Phi \rangle = \langle \Psi \mid \Phi \rangle$)
    clona dos estados normalizados $\lvert\psi\rangle$ y $\lvert\phi\rangle$ usando un estado blanco
    fijo $\lvert e\rangle$ ($\langle e \mid e \rangle = 1$):
    $$U(\lvert\psi\rangle \otimes \lvert e\rangle) = \lvert\psi\rangle \otimes \lvert\psi\rangle
      \quad \text{y} \quad
      U(\lvert\phi\rangle \otimes \lvert e\rangle) = \lvert\phi\rangle \otimes \lvert\phi\rangle.$$
    Entonces **forzosamente** $\langle\psi \mid \phi\rangle = 0$ (son ortogonales) o
    $\langle\psi \mid \phi\rangle = 1$ (son colineales/idénticos). ¡No existe ningún clonador
    cuántico universal! -/
theorem no_cloning_theorem
    (U : Ket4 → Ket4)
    (hIso : ∀ Ψ Φ : Ket4, braket4 (U Ψ) (U Φ) = braket4 Ψ Φ)
    (e ψ φ : Ket2)
    (heNorm : braket e e = Cplx.one)
    (hCloneΨ : U (tensorKet ψ e) = tensorKet ψ ψ)
    (hCloneΦ : U (tensorKet φ e) = tensorKet φ φ) :
    braket ψ φ = Cplx.zero ∨ braket ψ φ = Cplx.one := by
  have hEq : Cplx.mul (braket ψ φ) (braket ψ φ) = braket ψ φ := by
    calc
      Cplx.mul (braket ψ φ) (braket ψ φ)
        = braket4 (tensorKet ψ ψ) (tensorKet φ φ) := (braket4_tensorKet ψ ψ φ φ).symm
      _ = braket4 (U (tensorKet ψ e)) (U (tensorKet φ e)) := by rw [← hCloneΨ, ← hCloneΦ]
      _ = braket4 (tensorKet ψ e) (tensorKet φ e) := hIso _ _
      _ = Cplx.mul (braket ψ φ) (braket e e) := braket4_tensorKet ψ e φ e
      _ = braket ψ φ := by
            rw [heNorm, Cplx.mul_one]
  exact cplx_idempotent_zero_or_one (braket ψ φ) hEq

/-! ## 2. Protocolo de Teleportación Cuántica de 3 Qubits (Bennett et al., 1993) -/

/-- Estado de 3 qubits $(A, B, C) \in \mathcal{H}_2^{\otimes 3} \cong \mathbb{C}^8$, donde:
    - Qubit $A$: estado secreto $\lvert\psi\rangle = \alpha\lvert 0\rangle + \beta\lvert 1\rangle$ de Alice.
    - Qubits $(B, C)$: par EPR entrelazado $\lvert\Phi^+\rangle_{BC}$ compartido entre Alice ($B$) y Bob ($C$). -/
structure Ket8 where
  a000 : Cplx
  a001 : Cplx
  a010 : Cplx
  a011 : Cplx
  a100 : Cplx
  a101 : Cplx
  a110 : Cplx
  a111 : Cplx
  deriving Repr, DecidableEq

/-- Estado inicial tripartito $\lvert\psi\rangle_A \otimes \lvert\Phi^+\rangle_{BC}$: -/
def teleportInit (ψ : Ket2) : Ket8 :=
  { a000 := ψ.c0, a001 := Cplx.zero, a010 := Cplx.zero, a011 := ψ.c0
  , a100 := ψ.c1, a101 := Cplx.zero, a110 := Cplx.zero, a111 := ψ.c1 }

/-- Paso 1 de Alice: puerta `CNOT` de su qubit $A$ hacia su mitad $B$ del par de Bell -/
def aliceCNOT_AB (s : Ket8) : Ket8 :=
  { a000 := s.a000, a001 := s.a001, a010 := s.a010, a011 := s.a011
  , a100 := s.a110, a101 := s.a111, a110 := s.a100, a111 := s.a101 }

/-- Paso 2 de Alice: puerta Hadamard $\tilde{H} = \sqrt{2} H$ sobre su qubit $A$ -/
def aliceH_A (s : Ket8) : Ket8 :=
  { a000 := Cplx.add s.a000 s.a100
  , a001 := Cplx.add s.a001 s.a101
  , a010 := Cplx.add s.a010 s.a110
  , a011 := Cplx.add s.a011 s.a111
  , a100 := Cplx.sub s.a000 s.a100
  , a101 := Cplx.sub s.a001 s.a101
  , a110 := Cplx.sub s.a010 s.a110
  , a111 := Cplx.sub s.a011 s.a111 }

/-- Paso 3: Alice mide sus dos qubits $(A, B)$ obteniendo los bits clásicos $(m_1, m_2) \in \text{Bool}^2$;
    extraemos el estado post-medición colapsado del qubit $C$ en manos de Bob: -/
def projectBobQubit (s : Ket8) (m1 m2 : Bool) : Ket2 :=
  match m1, m2 with
  | false, false => ⟨s.a000, s.a001⟩ -- resultado 00
  | false, true  => ⟨s.a010, s.a011⟩ -- resultado 01
  | true,  false => ⟨s.a100, s.a101⟩ -- resultado 10
  | true,  true  => ⟨s.a110, s.a111⟩ -- resultado 11

/-- Paso 4: Bob recibe los 2 bits clásicos $(m_1, m_2)$ por teléfono/fibra óptica y aplica la
    corrección condicional de Pauli $Z^{m_1} X^{m_2}$ (primero $X$ si $m_2$, luego $Z$ si $m_1$!): -/
def bobCorrection (m1 m2 : Bool) (q : Ket2) : Ket2 :=
  let afterX := if m2 then applyMat2 pauliX q else q
  if m1 then applyMat2 pauliZ afterX else afterX

/-- Protocolo completo de teleportación cuántica extremo a extremo para la rama $(m_1, m_2)$: -/
def runTeleportationBranch (ψ : Ket2) (m1 m2 : Bool) : Ket2 :=
  let preMeas := aliceH_A (aliceCNOT_AB (teleportInit ψ))
  bobCorrection m1 m2 (projectBobQubit preMeas m1 m2)

/-- **TEOREMA DE CORRECCIÓN UNIVERSAL DE LA TELEPORTACIÓN CUÁNTICA (`teleportation_exact_recovery`):**
    Para **cualquier** estado cuántico complejo arbitrario $\lvert\psi\rangle \in \mathcal{H}_2$ y
    para **cualquiera** de los 4 resultados equiprobables $(m_1, m_2) \in \{\text{false}, \text{true}\}^2$
    de la medición de Alice, tras aplicar `bobCorrection m1 m2`, el qubit de Bob coincide
    **idénticamente** con $\lvert\psi\rangle$! -/
theorem teleportation_exact_recovery (ψ : Ket2) (m1 m2 : Bool) :
    runTeleportationBranch ψ m1 m2 = ψ := by
  cases ψ with | mk c0 c1 =>
  cases c0; cases c1
  cases m1 <;> cases m2 <;> {
    dsimp [runTeleportationBranch, teleportInit, aliceCNOT_AB, aliceH_A,
           projectBobQubit, bobCorrection, applyMat2, pauliX, pauliZ,
           Cplx.add, Cplx.sub, Cplx.mul, Cplx.zero]
    simp only [Ket2.mk.injEq, Cplx.mk.injEq]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  }

/-! ## 3. Algoritmo Cuántico de Deutsch (Interferencia y *Phase Kickback*) -/

/-- Signo de fase $(-1)^{f(x)} \in \mathbb{Z}[i]$ inducido por el retroceso de fase (*Phase Kickback*)
    sobre el estado auxiliar $\lvert -\rangle$: -/
def phaseSign (b : Bool) : Cplx :=
  if b then ⟨-1, 0⟩ else ⟨1, 0⟩

/-- Oráculo de fase $U_f$ actuando sobre el primer qubit tras preparar $\lvert +\rangle = \tilde{H}\lvert 0\rangle$:
    envía $\lvert 0\rangle + \lvert 1\rangle \mapsto (-1)^{f(\text{false})}\lvert 0\rangle + (-1)^{f(\text{true})}\lvert 1\rangle$. -/
def deutschQuery (f : Bool → Bool) : Ket2 :=
  applyMat2 hadamardScaled ⟨phaseSign (f false), phaseSign (f true)⟩

/-- **TEOREMA DE CORRECCIÓN DEL ALGORITMO DE DEUTSCH (`deutsch_single_query_decides`):**
    Con **una sola evaluación** del oráculo cuántico `f`:
    1. Si `f` es **constante** ($f(\text{false}) = f(\text{true})$), la amplitud de medir $\lvert 1\rangle$ es **exactamente $0$**
       (interferencia destructiva total en $\lvert 1\rangle$!).
    2. Si `f` es **balanceada** ($f(\text{false}) \neq f(\text{true})$), la amplitud de medir $\lvert 0\rangle$ es **exactamente $0$**
       (certeza del 100% de medir $\lvert 1\rangle$!). -/
theorem deutsch_single_query_decides (f : Bool → Bool) :
    (f false = f true → (deutschQuery f).c1 = Cplx.zero) ∧
    (f false ≠ f true → (deutschQuery f).c0 = Cplx.zero) := by
  cases h0 : f false <;> cases h1 : f true <;> {
    dsimp [deutschQuery, phaseSign, applyMat2, hadamardScaled, Cplx.add, Cplx.mul, Cplx.zero]
    rw [h0, h1]
    constructor <;> intro h <;> first | contradiction | rfl
  }

-- Demostración ejecutable: teleportando el estado complejo (3 + 4i)|0⟩ + (-2 + 5i)|1⟩ en la rama (true, true)
#eval runTeleportationBranch ⟨⟨3, 4⟩, ⟨-2, 5⟩⟩ true true
-- Algoritmo de Deutsch distinguiendo `not` (balanceada) de `fun _ => true` (constante) en 1 consulta:
#eval deutschQuery not
#eval deutschQuery (fun _ => true)

end LeanTT.M79
