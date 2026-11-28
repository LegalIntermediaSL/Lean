import LeanTT.M77_PauliCliffordAlgebraAndUnitarity

/-!
# Módulo 78: Producto Tensorial $\mathcal{H}_A \otimes \mathcal{H}_B$, Estados de Bell y Prueba Formal de Entrelazamiento
En la física clásica, el estado de un sistema compuesto de dos partes es el producto cartesiano
$S_A \times S_B$ (siempre factorizable). En la **Mecánica Cuántica**, el espacio de estados es el
**producto tensorial** $\mathcal{H}_A \otimes \mathcal{H}_B \cong \mathbb{C}^4$, donde emergen
estados globalmente puros que **no poseen estados individuales definidos** en sus subsistemas: el
**Entrelazamiento Cuántico** (*Verschränkung*, Schrödinger 1935; EPR 1935; Bell 1964).

En este módulo formalizamos con `0 sorry`:
1. Vectores de 2 qubits (`Ket4`), producto tensorial de Kronecker $\lvert\psi\rangle \otimes \lvert\phi\rangle$
   (`tensorKet`) y circuito generador de Bell `CNOT ∘ (H ⊗ I)`.
2. Los **4 Estados de la Base de Bell** ($\lvert\Phi^+\rangle, \lvert\Phi^-\rangle, \lvert\Psi^+\rangle, \lvert\Psi^-\rangle$)
   y su **ortogonalidad mutua exacta**.
3. El **Invariante Determinantal de Segre-Schmidt** $\Delta(\Psi) = c_{00} c_{11} - c_{01} c_{10}$:
   - Demostramos que **todo estado separable** $\lvert u\rangle \otimes \lvert v\rangle$ satisface
     idénticamente $\Delta(\lvert u\rangle \otimes \lvert v\rangle) = 0$.
   - Deducimos el **Teorema Formal de Inseparabilidad / Entrelazamiento (`bellPhiPlus_entangled`)**:
     **no existen** estados de 1 qubit $\lvert u\rangle, \lvert v\rangle \in \mathcal{H}_2$ tales que
     $\lvert u\rangle \otimes \lvert v\rangle = \lvert\Phi^+\rangle$!
-/

namespace LeanTT.M78

open LeanTT.M76
open LeanTT.M77

/-- Estado cuántico de 2 qubits $\lvert\Psi\rangle = c_{00}\lvert 00\rangle + c_{01}\lvert 01\rangle + c_{10}\lvert 10\rangle + c_{11}\lvert 11\rangle \in \mathcal{H}_2 \otimes \mathcal{H}_2$ -/
structure Ket4 where
  c00 : Cplx
  c01 : Cplx
  c10 : Cplx
  c11 : Cplx
  deriving Repr, DecidableEq

/-- Producto tensorial de Kronecker $\lvert u\rangle \otimes \lvert v\rangle$: -/
def tensorKet (u v : Ket2) : Ket4 :=
  { c00 := Cplx.mul u.c0 v.c0
  , c01 := Cplx.mul u.c0 v.c1
  , c10 := Cplx.mul u.c1 v.c0
  , c11 := Cplx.mul u.c1 v.c1 }

/-- Producto interno sesquilineal en $\mathcal{H}_4$: -/
def braket4 (Ψ Φ : Ket4) : Cplx :=
  Cplx.add
    (Cplx.add (Cplx.mul (Cplx.conj Ψ.c00) Φ.c00) (Cplx.mul (Cplx.conj Ψ.c01) Φ.c01))
    (Cplx.add (Cplx.mul (Cplx.conj Ψ.c10) Φ.c10) (Cplx.mul (Cplx.conj Ψ.c11) Φ.c11))

/-! ## 1. Circuito Cuántico de Preparación de la Base de Bell (`CNOT ∘ (H ⊗ I)`) -/

/-- Aplicación de $(\tilde{H} \otimes I)$ sobre el primer qubit de un `Ket4`: -/
def applyH1 (Ψ : Ket4) : Ket4 :=
  { c00 := Cplx.add Ψ.c00 Ψ.c10
  , c01 := Cplx.add Ψ.c01 Ψ.c11
  , c10 := Cplx.sub Ψ.c00 Ψ.c10
  , c11 := Cplx.sub Ψ.c01 Ψ.c11 }

/-- Puerta entrelazadora `CNOT` (control = qubit 1, objetivo = qubit 2): intercambia amplitudes $\lvert 10\rangle \leftrightarrow \lvert 11\rangle$ -/
def applyCNOT12 (Ψ : Ket4) : Ket4 :=
  { c00 := Ψ.c00
  , c01 := Ψ.c01
  , c10 := Ψ.c11
  , c11 := Ψ.c10 }

/-- Los 4 estados máximamente entrelazados de **Bell / EPR** (escalados por $\sqrt{2}$): -/
def bellPhiPlus  : Ket4 := applyCNOT12 (applyH1 (tensorKet ket0 ket0)) -- |00⟩ + |11⟩
def bellPhiMinus : Ket4 := applyCNOT12 (applyH1 (tensorKet ket1 ket0)) -- |00⟩ - |11⟩
def bellPsiPlus  : Ket4 := applyCNOT12 (applyH1 (tensorKet ket0 ket1)) -- |01⟩ + |10⟩
def bellPsiMinus : Ket4 := applyCNOT12 (applyH1 (tensorKet ket1 ket1)) -- |01⟩ - |10⟩

theorem bellPhiPlus_explicit :
    bellPhiPlus = ⟨Cplx.one, Cplx.zero, Cplx.zero, Cplx.one⟩ := rfl

/-- **ORTOGONALIDAD MUTUA DE LA BASE DE BELL (`bell_basis_orthogonal`):**
    Los cuatro estados de Bell forman una base ortogonal exacta de $\mathcal{H}_2 \otimes \mathcal{H}_2$. -/
theorem bell_basis_orthogonal :
    braket4 bellPhiPlus bellPhiMinus = Cplx.zero ∧
    braket4 bellPhiPlus bellPsiPlus  = Cplx.zero ∧
    braket4 bellPhiPlus bellPsiMinus = Cplx.zero ∧
    braket4 bellPhiMinus bellPsiPlus = Cplx.zero ∧
    braket4 bellPhiMinus bellPsiMinus = Cplx.zero ∧
    braket4 bellPsiPlus bellPsiMinus = Cplx.zero := by
  decide

/-! ## 2. Invariante de Segre-Schmidt y Demostración Formal del Entrelazamiento Cuántico -/

/-- Predicado de estado producto (separable / no entrelazado): -/
def IsSeparable (Ψ : Ket4) : Prop :=
  ∃ u v : Ket2, tensorKet u v = Ψ

/-- Determinante cuadrático de concurrencia/Schmidt (complejo): $\Delta(\Psi) = c_{00} c_{11} - c_{01} c_{10}$ -/
def schmidtDet (Ψ : Ket4) : Cplx :=
  Cplx.sub (Cplx.mul Ψ.c00 Ψ.c11) (Cplx.mul Ψ.c01 Ψ.c10)

/-- Asociatividad/conmutatividad del producto en $\mathbb{Z}[i]$ para $(u_0 v_0)(u_1 v_1) = (u_0 v_1)(u_1 v_0)$: -/
private theorem cplx_mul_four_swap (a b c d : Cplx) :
    Cplx.mul (Cplx.mul a b) (Cplx.mul c d) = Cplx.mul (Cplx.mul a d) (Cplx.mul c b) := by
  rw [Cplx.mul_comm c d, Cplx.mul4_swap a b d c, Cplx.mul_comm b c]

/-- **LEMA DE ANULACIÓN DE SEGRE-SCHMIDT (`separable_schmidtDet_zero`):**
    Todo estado cuántico separable $\Psi = \lvert u\rangle \otimes \lvert v\rangle$ tiene determinante
    de Schmidt idénticamente cero ($\Delta(\Psi) = 0$)! -/
theorem separable_schmidtDet_zero {Ψ : Ket4} (hSep : IsSeparable Ψ) :
    schmidtDet Ψ = Cplx.zero := by
  rcases hSep with ⟨u, v, rfl⟩
  dsimp [schmidtDet, tensorKet]
  rw [cplx_mul_four_swap u.c0 v.c0 u.c1 v.c1]
  cases Cplx.mul (Cplx.mul u.c0 v.c1) (Cplx.mul u.c1 v.c0)
  dsimp [Cplx.sub, Cplx.zero]
  simp only [Cplx.mk.injEq]
  exact ⟨by omega, by omega⟩

/-- **TEOREMA DE EXISTENCIA DEL ENTRELAZAMIENTO CUÁNTICO (`bellPhiPlus_not_separable`):**
    El par EPR $\lvert\Phi^+\rangle = \lvert 00\rangle + \lvert 11\rangle$ **NO es separable**:
    es matemáticamente imposible factorizarlo como $\lvert u\rangle \otimes \lvert v\rangle$
    para ningún par de estados locales $\lvert u\rangle, \lvert v\rangle \in \mathcal{H}_2$! -/
theorem bellPhiPlus_not_separable : ¬ IsSeparable bellPhiPlus := by
  intro hSep
  have hZero := separable_schmidtDet_zero hSep
  -- Pero para |Φ⁺⟩ = (1, 0, 0, 1), el determinante de Schmidt vale exactamente 1 ≠ 0!
  have hOne : schmidtDet bellPhiPlus = Cplx.one := rfl
  rw [hOne] at hZero
  injection hZero with h1 _
  omega

/-- Los 4 estados de la base de Bell están todos genuinamente entrelazados: -/
theorem all_bell_states_entangled :
    ¬ IsSeparable bellPhiPlus ∧
    ¬ IsSeparable bellPhiMinus ∧
    ¬ IsSeparable bellPsiPlus ∧
    ¬ IsSeparable bellPsiMinus := by
  refine ⟨bellPhiPlus_not_separable, ?_, ?_, ?_⟩ <;> {
    intro hSep
    have hZero := separable_schmidtDet_zero hSep
    revert hZero
    decide
  }

-- Demostración ejecutable: determinante de concurrencia de |0⟩⊗|+⟩ (= 0) frente a |Φ⁺⟩ (= 1 + 0i)
#eval schmidtDet (tensorKet ket0 ketPlus)
#eval schmidtDet bellPhiPlus

end LeanTT.M78
