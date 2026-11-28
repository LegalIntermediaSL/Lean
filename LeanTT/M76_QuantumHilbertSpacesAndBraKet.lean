/-!
# Módulo 76: Espacios de Hilbert Cuánticos ($\mathbb{Z}[i]$), Notación Bra-Ket de Dirac y Observables Hermíticos
Los postulados de Dirac-von Neumann fundamentan la Mecánica Cuántica sobre espacios de Hilbert
complejos $\mathcal{H}$:
1. **Amplitudes Complejas Exactas (`Cplx` sobre $\mathbb{Z}[i]$):** leyes de anillo conmutativo,
   conjugación $z^*$, módulo al cuadrado $|z|^2 = a^2 + b^2 \ge 0$ (Regla de Born) y demostración
   formal de la **Identidad de Brahmagupta-Fibonacci** ($|z \cdot w|^2 = |z|^2 \cdot |w|^2$).
2. **Vectores Ket de 1 Qubit (`Ket2`) y Producto Interno Sesquilineal $\langle \psi \mid \phi \rangle$
   (`braket`):**
   - Simetría hermítica conjugada: $\langle \psi \mid \phi \rangle = \langle \phi \mid \psi \rangle^*$.
   - Positividad estricta de la norma: $\text{Im}\langle \psi \mid \psi \rangle = 0$ y
     $\text{Re}\langle \psi \mid \psi \rangle \ge 0$, anulándose si y solo si $\lvert\psi\rangle = 0$.
3. **Observables Hermíticos ($A^\dagger = A$):** demostración formal del teorema espectral elemental
   de la mecánica cuántica: **el valor esperado $\langle \psi \mid A \psi \rangle$ de todo operador
   hermítico es estrictamente real** ($\text{Im}\langle \psi \mid A \psi \rangle = 0$ para todo $\lvert\psi\rangle$)!
-/

namespace LeanTT.M76

/-- Lema auxiliar entero: todo cuadrado en $\mathbb{Z}$ es no negativo ($0 \le x \cdot x$) -/
theorem int_sq_nonneg (x : Int) : 0 ≤ x * x := by
  rcases Int.le_total 0 x with h | h
  · exact Int.mul_nonneg h h
  · have h' : 0 ≤ -x := by omega
    have hEq : (-x) * (-x) = x * x := by simp [Int.neg_mul, Int.mul_neg]
    rw [← hEq]
    exact Int.mul_nonneg h' h'

/-- Lema auxiliar entero de intercambio medio en un producto cuádruple $(p q)(r s) = (p r)(q s)$: -/
theorem int_mul4_swap (p q r s : Int) : (p * q) * (r * s) = (p * r) * (q * s) := by
  rw [Int.mul_assoc p q (r * s), ← Int.mul_assoc q r s, Int.mul_comm q r,
      Int.mul_assoc r q s, ← Int.mul_assoc p r (q * s)]

/-- Escalar complejo exacto $z = \text{re} + i\cdot\text{im} \in \mathbb{Z}[i]$ (enteros de Gauss) -/
structure Cplx where
  re : Int
  im : Int
  deriving Repr, DecidableEq

namespace Cplx

def zero  : Cplx := ⟨0, 0⟩
def one   : Cplx := ⟨1, 0⟩
def iUnit : Cplx := ⟨0, 1⟩

def add  (z w : Cplx) : Cplx := ⟨z.re + w.re, z.im + w.im⟩
def sub  (z w : Cplx) : Cplx := ⟨z.re - w.re, z.im - w.im⟩
def neg  (z : Cplx)   : Cplx := ⟨-z.re, -z.im⟩
def conj (z : Cplx)   : Cplx := ⟨z.re, -z.im⟩

def mul (z w : Cplx) : Cplx :=
  ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

/-- Módulo cuadrático de Born $|z|^2 = z^* z = \text{re}^2 + \text{im}^2$ -/
def normSq (z : Cplx) : Int :=
  z.re * z.re + z.im * z.im

/-! ### Estructura de Anillo Conmutativo con Involución ($\mathbb{Z}[i]$) -/

@[simp]
theorem conj_conj (z : Cplx) : conj (conj z) = z := by
  cases z; dsimp [conj]; simp only [Cplx.mk.injEq]; exact ⟨trivial, by omega⟩

@[simp]
theorem iUnit_sq : mul iUnit iUnit = ⟨-1, 0⟩ := rfl

theorem add_comm (z w : Cplx) : add z w = add w z := by
  cases z; cases w; dsimp [add]; simp only [Cplx.mk.injEq]; exact ⟨by omega, by omega⟩

theorem add_assoc (u v w : Cplx) : add (add u v) w = add u (add v w) := by
  cases u; cases v; cases w; dsimp [add]; simp only [Cplx.mk.injEq]; exact ⟨by omega, by omega⟩

theorem add_left_comm (u v w : Cplx) : add u (add v w) = add v (add u w) := by
  rw [← add_assoc, add_comm u v, add_assoc]

@[simp]
theorem add_zero (z : Cplx) : add z zero = z := by
  cases z; dsimp [add, zero]; simp only [Cplx.mk.injEq]; exact ⟨by omega, by omega⟩

@[simp]
theorem zero_add (z : Cplx) : add zero z = z := by
  cases z; dsimp [add, zero]; simp only [Cplx.mk.injEq]; exact ⟨by omega, by omega⟩

@[simp]
theorem mul_one (z : Cplx) : mul z one = z := by
  cases z; dsimp [mul, one]; simp only [Cplx.mk.injEq]; exact ⟨by omega, by omega⟩

@[simp]
theorem one_mul (z : Cplx) : mul one z = z := by
  cases z; dsimp [mul, one]; simp only [Cplx.mk.injEq]; exact ⟨by omega, by omega⟩

theorem mul_comm (z w : Cplx) : mul z w = mul w z := by
  cases z with | mk ar ai =>
  cases w with | mk br bi =>
  dsimp [mul]
  rw [Int.mul_comm ar br, Int.mul_comm ai bi, Int.mul_comm ar bi, Int.mul_comm ai br]
  simp only [Cplx.mk.injEq]
  exact ⟨trivial, by omega⟩

theorem mul_assoc (u v w : Cplx) : mul (mul u v) w = mul u (mul v w) := by
  cases u; cases v; cases w
  dsimp [mul]
  simp only [Cplx.mk.injEq, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
  exact ⟨by omega, by omega⟩

theorem mul_add (u v w : Cplx) : mul u (add v w) = add (mul u v) (mul u w) := by
  cases u; cases v; cases w
  dsimp [mul, add]
  simp only [Cplx.mk.injEq, Int.mul_add]
  exact ⟨by omega, by omega⟩

theorem add_mul (u v w : Cplx) : mul (add u v) w = add (mul u w) (mul v w) := by
  rw [mul_comm, mul_add, mul_comm u w, mul_comm v w]

theorem mul4_swap (a b c d : Cplx) : mul (mul a b) (mul c d) = mul (mul a c) (mul b d) := by
  rw [mul_assoc a b (mul c d), ← mul_assoc b c d, mul_comm b c,
      mul_assoc c b d, ← mul_assoc a c (mul b d)]

theorem conj_add (z w : Cplx) : conj (add z w) = add (conj z) (conj w) := by
  cases z; cases w; dsimp [conj, add]; simp only [Cplx.mk.injEq]; exact ⟨trivial, by omega⟩

theorem conj_mul (z w : Cplx) : conj (mul z w) = mul (conj z) (conj w) := by
  cases z with | mk ar ai =>
  cases w with | mk br bi =>
  dsimp [conj, mul]
  simp only [Cplx.mk.injEq, Int.neg_mul, Int.mul_neg]
  exact ⟨by omega, by omega⟩

theorem conj_mul_self (z : Cplx) : mul (conj z) z = ⟨normSq z, 0⟩ := by
  cases z with | mk a b =>
  dsimp [conj, mul, normSq]
  simp only [Cplx.mk.injEq, Int.neg_mul]
  rw [Int.mul_comm b a]
  exact ⟨by omega, by omega⟩

/-- No negatividad de las probabilidades de Born: $|z|^2 \ge 0$ para todo $z \in \mathbb{Z}[i]$ -/
theorem normSq_nonneg (z : Cplx) : 0 ≤ normSq z := by
  dsimp [normSq]
  have h1 := int_sq_nonneg z.re
  have h2 := int_sq_nonneg z.im
  omega

/-- Anulación del módulo cuadrático: $|z|^2 = 0 \iff z = 0$ -/
theorem normSq_eq_zero_iff (z : Cplx) : normSq z = 0 ↔ z = zero := by
  cases z with | mk a b =>
  dsimp [normSq, zero]
  constructor
  · intro h
    have ha := int_sq_nonneg a
    have hb := int_sq_nonneg b
    have ha0 : a * a = 0 := by omega
    have hb0 : b * b = 0 := by omega
    rcases Int.mul_eq_zero.mp ha0 with rfl | rfl <;>
    rcases Int.mul_eq_zero.mp hb0 with rfl | rfl <;> rfl
  · rintro ⟨⟩; rfl

/-- **IDENTIDAD DE BRAHMAGUPTA-FIBONACCI (`normSq_mul`):**
    El módulo cuadrático es multiplicativo: $|z \cdot w|^2 = |z|^2 \cdot |w|^2$. -/
theorem normSq_mul (z w : Cplx) : normSq (mul z w) = normSq z * normSq w := by
  cases z with | mk a b =>
  cases w with | mk c d =>
  dsimp [normSq, mul]
  have sq1 : (a * c - b * d) * (a * c - b * d) =
      (a * a) * (c * c) - 2 * ((a * b) * (c * d)) + (b * b) * (d * d) := by
    simp only [Int.sub_mul, Int.mul_sub]
    rw [int_mul4_swap a c a c, int_mul4_swap a c b d,
        Int.mul_comm (b * d) (a * c), int_mul4_swap a c b d, int_mul4_swap b d b d]
    omega
  have sq2 : (a * d + b * c) * (a * d + b * c) =
      (a * a) * (d * d) + 2 * ((a * b) * (c * d)) + (b * b) * (c * c) := by
    simp only [Int.add_mul, Int.mul_add]
    rw [int_mul4_swap a d a d, int_mul4_swap a d b c, Int.mul_comm d c,
        Int.mul_comm (b * c) (a * d), int_mul4_swap a d b c, Int.mul_comm d c,
        int_mul4_swap b c b c]
    omega
  rw [sq1, sq2]
  simp only [Int.add_mul, Int.mul_add]
  omega

end Cplx

/-! ## 2. Vectores de Estado de 1 Qubit (`Ket2`) y Producto Interno Bra-Ket $\langle \psi \mid \phi \rangle$ -/

/-- Estado cuántico $\lvert\psi\rangle = c_0 \lvert 0\rangle + c_1 \lvert 1\rangle \in \mathcal{H}_2$ -/
structure Ket2 where
  c0 : Cplx
  c1 : Cplx
  deriving Repr, DecidableEq

/-- Base computacional $\lvert 0\rangle, \lvert 1\rangle$ y estados de superposición $\lvert +\rangle, \lvert -\rangle$ (escalados por $\sqrt{2}$) -/
def ket0     : Ket2 := ⟨Cplx.one, Cplx.zero⟩
def ket1     : Ket2 := ⟨Cplx.zero, Cplx.one⟩
def ketPlus  : Ket2 := ⟨Cplx.one, Cplx.one⟩
def ketMinus : Ket2 := ⟨Cplx.one, ⟨-1, 0⟩⟩

/-- Producto interno sesquilineal de Dirac $\langle \psi \mid \phi \rangle = \psi_0^* \phi_0 + \psi_1^* \phi_1$: -/
def braket (ψ φ : Ket2) : Cplx :=
  Cplx.add (Cplx.mul (Cplx.conj ψ.c0) φ.c0) (Cplx.mul (Cplx.conj ψ.c1) φ.c1)

/-- Ortogonalidad exacta de $\lvert 0\rangle$ y $\lvert 1\rangle$, y de $\lvert +\rangle$ y $\lvert -\rangle$: -/
theorem basis_orthogonal : braket ket0 ket1 = Cplx.zero ∧ braket ketPlus ketMinus = Cplx.zero := by
  decide

/-- **SIMETRÍA CONJUGADA DEL PRODUCTO INTERNO (`braket_conj_symm`):**
    $$\langle \psi \mid \phi \rangle = \langle \phi \mid \psi \rangle^*.$$ -/
theorem braket_conj_symm (ψ φ : Ket2) : braket ψ φ = Cplx.conj (braket φ ψ) := by
  dsimp [braket]
  rw [Cplx.conj_add, Cplx.conj_mul, Cplx.conj_mul, Cplx.conj_conj, Cplx.conj_conj]
  rw [Cplx.mul_comm φ.c0 (Cplx.conj ψ.c0), Cplx.mul_comm φ.c1 (Cplx.conj ψ.c1)]

/-- **POSITIVIDAD Y REALIDAD DE LA NORMA CUÁNTICA (`braket_self_real_nonneg`):**
    $\langle \psi \mid \psi \rangle = (|c_0|^2 + |c_1|^2) + 0i$ con parte real $\ge 0$. -/
theorem braket_self_real_nonneg (ψ : Ket2) :
    braket ψ ψ = ⟨Cplx.normSq ψ.c0 + Cplx.normSq ψ.c1, 0⟩ ∧
      0 ≤ (braket ψ ψ).re := by
  dsimp [braket]
  rw [Cplx.conj_mul_self, Cplx.conj_mul_self]
  dsimp [Cplx.add]
  refine ⟨rfl, ?_⟩
  have h0 := Cplx.normSq_nonneg ψ.c0
  have h1 := Cplx.normSq_nonneg ψ.c1
  omega

/-! ## 3. Operadores Lineales $2\times 2$, Adjunto Hermítico $A^\dagger$ y Realidad de Valores Esperados -/

structure Mat2C where
  m00 : Cplx
  m01 : Cplx
  m10 : Cplx
  m11 : Cplx
  deriving Repr, DecidableEq

/-- Acción de un operador $A$ sobre un ket $\lvert\psi\rangle$: $A\lvert\psi\rangle$ -/
def applyMat2 (A : Mat2C) (ψ : Ket2) : Ket2 :=
  { c0 := Cplx.add (Cplx.mul A.m00 ψ.c0) (Cplx.mul A.m01 ψ.c1)
  , c1 := Cplx.add (Cplx.mul A.m10 ψ.c0) (Cplx.mul A.m11 ψ.c1) }

/-- Adjunto hermítico (traspuesta conjugada) $A^\dagger = (A^T)^*$ -/
def dagger2 (A : Mat2C) : Mat2C :=
  { m00 := Cplx.conj A.m00
  , m01 := Cplx.conj A.m10
  , m10 := Cplx.conj A.m01
  , m11 := Cplx.conj A.m11 }

abbrev IsHermitian (A : Mat2C) : Prop := dagger2 A = A

/-- Propiedad definitoria del adjunto hermítico demostrada limpiamente en el anillo $\mathbb{Z}[i]$:
    $\langle A^\dagger \psi \mid \phi \rangle = \langle \psi \mid A \phi \rangle$. -/
theorem braket_dagger_left (A : Mat2C) (ψ φ : Ket2) :
    braket (applyMat2 (dagger2 A) ψ) φ = braket ψ (applyMat2 A φ) := by
  dsimp [braket, applyMat2, dagger2]
  simp only [Cplx.conj_add, Cplx.conj_mul, Cplx.conj_conj,
             Cplx.add_mul, Cplx.mul_add]
  rw [Cplx.mul_comm A.m00 (Cplx.conj ψ.c0), Cplx.mul_comm A.m10 (Cplx.conj ψ.c1),
      Cplx.mul_comm A.m01 (Cplx.conj ψ.c0), Cplx.mul_comm A.m11 (Cplx.conj ψ.c1)]
  simp only [Cplx.mul_assoc, Cplx.add_assoc]
  rw [Cplx.add_left_comm (Cplx.mul (Cplx.conj ψ.c1) (Cplx.mul A.m10 φ.c0))]

/-- **TEOREMA FUNDAMENTAL DE LOS OBSERVABLES CUÁNTICOS (`hermitian_expectation_is_real`):**
    Si $A$ es un observable hermítico ($A^\dagger = A$), entonces para **todo** estado cuántico
    $\lvert\psi\rangle \in \mathcal{H}_2$, su valor esperado $\langle \psi \mid A \psi \rangle$
    tiene parte imaginaria **idénticamente cero** ($\langle \psi \mid A \psi \rangle \in \mathbb{R}$)! -/
theorem hermitian_expectation_is_real {A : Mat2C} (hHerm : IsHermitian A) (ψ : Ket2) :
    (braket ψ (applyMat2 A ψ)).im = 0 := by
  have hAdj : braket ψ (applyMat2 A ψ) = Cplx.conj (braket ψ (applyMat2 A ψ)) := by
    calc
      braket ψ (applyMat2 A ψ)
        = braket (applyMat2 (dagger2 A) ψ) ψ := (braket_dagger_left A ψ ψ).symm
      _ = braket (applyMat2 A ψ) ψ           := by rw [hHerm]
      _ = Cplx.conj (braket ψ (applyMat2 A ψ)) := braket_conj_symm (applyMat2 A ψ) ψ
  have hIm := congrArg Cplx.im hAdj
  dsimp [Cplx.conj] at hIm
  omega

#eval Cplx.normSq (braket ket0 ketPlus)
#eval braket ketPlus ketPlus

end LeanTT.M76
