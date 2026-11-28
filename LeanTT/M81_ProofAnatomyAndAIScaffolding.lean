/-!
# Módulo 81: Anatomía Paso a Paso de una Demostración en Lean 4 y Andamiaje Formal para IA (*Blueprints*)
Este módulo acompaña al artículo [`docs/24_articulo_anatomia_demostracion_lean4_e_ia.md`](../docs/24_articulo_anatomia_demostracion_lean4_e_ia.md)
y a los 5 cuadernos interactivos en [`docs/cuadernos_demostracion_e_ia/`](../docs/cuadernos_demostracion_e_ia/00_indice_cuadernos_demostracion_e_ia.md)
y [`notebooks/`](../notebooks/).

Reúne tres estudios de caso completos (`0 sorry`, `0 warnings`) que ilustran tanto la **metodología
humana paso a paso** como la **ingeniería de descomposición (*Blueprint* + *Compiler-in-the-Loop* +
*Spec-Audit*)** empleada para instruir a agentes de IA en Lean 4:

1. **Estudio de Caso 1 — El Teorema de Nicómaco ($\sum_{k=0}^n k^3 = (\sum_{k=0}^n k)^2$):**
   Demostración estructurada mediante *Blueprint* jerárquico de 4 etapas (especificación computable
   $\to$ lema de Gauss $\to$ lema algebraico de transición $\to$ ensamblaje inductivo con `calc` y
   especialización exacta a $(\sum k)^2$).
2. **Estudio de Caso 2 — Por Qué Se Atasca una Inducción Ingenua y Cómo Desbloquearla (`fastRev`):**
   Verificación de la inversión de listas en tiempo lineal $O(n)$ con acumulador (`revAcc`),
   mostrando el patrón esencial `induction xs generalizing acc`.
3. **Estudio de Caso 3 — Auditoría Anti-Alucinación de Especificaciones (*Spec-Audit*):**
   Cómo exigir a una IA pruebas formales de **No-Vacuidad** ($\exists x,\, \text{Pre}(x)$) y
   ausencia de axiomas espurios para impedir especificaciones trivialmente verdaderas.
-/

namespace LeanTT.M81

/-! ## Estudio de Caso 1: El Teorema de Nicómaco de Gerasa (c. 100 d. C.) Paso a Paso

Queremos demostrar que la suma de los primeros $n$ cubos perfectos es exactamente igual al cuadrado
de la suma de los primeros $n$ naturales:
$$\sum_{k=0}^n k^3 = \left(\sum_{k=0}^n k\right)^2.$$

### Regla de Diseño #1 (tanto para humanos como para IA):
Evita la división entera truncada `/` de `Nat` en los lemas intermedios! En lugar de escribir
$\sum_{k=0}^n k = \frac{n(n+1)}{2}$, formulamos la identidad multiplicada por $2$:
$$2 \sum_{k=0}^n k = n(n+1) \quad \text{y} \quad 4 \sum_{k=0}^n k^3 = \big(n(n+1)\big)^2,$$
y al final dividimos limpiamente cancelando el factor $4$ entre números naturales! -/

/-- Suma recursiva de los primeros naturales $0 + 1 + \dots + n$ -/
def sumN : Nat → Nat
  | 0     => 0
  | n + 1 => sumN n + (n + 1)

/-- Suma recursiva de los primeros cubos $0^3 + 1^3 + \dots + n^3$ -/
def sumCubes : Nat → Nat
  | 0     => 0
  | n + 1 => sumCubes n + (n + 1) * (n + 1) * (n + 1)

/-- **LEMA 1 DEL BLUEPRINT (Identidad de Gauss sin división):**
    $2 \cdot \sum_{k=0}^n k = n(n + 1)$. -/
theorem two_mul_sumN (n : Nat) : 2 * sumN n = n * (n + 1) := by
  -- Estado inicial del Infoview: `n : Nat ⊢ 2 * sumN n = n * (n + 1)`
  induction n with
  | zero =>
    -- Caso base `n = 0`: `2 * 0 = 0 * 1`, cierto por cálculo definicional (`rfl`)
    rfl
  | succ k ih =>
    -- Hipótesis inductiva `ih : 2 * sumN k = k * (k + 1)`
    -- Meta: `2 * sumN (k + 1) = (k + 1) * (k + 2)`
    calc
      2 * sumN (k + 1)
        = 2 * (sumN k + (k + 1))         := rfl
      _ = 2 * sumN k + 2 * (k + 1)       := Nat.mul_add 2 (sumN k) (k + 1)
      _ = k * (k + 1) + 2 * (k + 1)      := by rw [ih]
      _ = (k + 2) * (k + 1)              := (Nat.add_mul k 2 (k + 1)).symm
      _ = (k + 1) * (k + 2)              := Nat.mul_comm (k + 2) (k + 1)

/-- **LEMA 2 DEL BLUEPRINT (Paso Algebraico Aislado de Nicómaco):**
    Aislamos la identidad polinómica de grado 4 fuera de la inducción para mantener la prueba modular:
    $$\big(k(k+1)\big)^2 + 4(k+1)^3 = \big((k+1)(k+2)\big)^2.$$
    Observa el factor común $(k+1)^2$: basta probar $k^2 + 4(k+1) = (k+2)^2$ y multiplicar por $(k+1)^2$! -/
theorem nicomachus_algebraic_step (k : Nat) :
    (k * (k + 1)) * (k * (k + 1)) + 4 * ((k + 1) * (k + 1) * (k + 1)) =
      ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) := by
  -- Paso 2.a: La identidad cuadrática núcleo `k² + 4(k + 1) = (k + 2)²` es elemental:
  have hQuad : k * k + 4 * (k + 1) = (k + 2) * (k + 2) := by
    calc
      k * k + 4 * (k + 1)
        = k * k + 4 * k + 4               := by omega
      _ = k * k + 2 * k + (2 * k + 4)     := by omega
      _ = k * (k + 2) + 2 * (k + 2)       := by rw [Nat.mul_add k k 2, Nat.mul_add 2 k 2]; omega
      _ = (k + 2) * (k + 2)               := (Nat.add_mul k 2 (k + 2)).symm
  -- Paso 2.b: Reordenamos `(a · b) · (a · b) = (a · a) · (b · b)` usando un micro-lema local:
  have sqMul (a b : Nat) : (a * b) * (a * b) = (a * a) * (b * b) := by
    rw [Nat.mul_assoc a b (a * b), ← Nat.mul_assoc b a b, Nat.mul_comm b a,
        Nat.mul_assoc a b b, ← Nat.mul_assoc a a (b * b)]
  -- Paso 2.c: Factorizamos `(k + 1) * (k + 1)` en todos los términos:
  let s := (k + 1) * (k + 1)
  have hTerm2 : 4 * (s * (k + 1)) = (4 * (k + 1)) * s := by
    rw [Nat.mul_comm s (k + 1), ← Nat.mul_assoc 4 (k + 1) s]
  calc
    (k * (k + 1)) * (k * (k + 1)) + 4 * ((k + 1) * (k + 1) * (k + 1))
      = (k * k) * s + (4 * (k + 1)) * s   := by rw [sqMul k (k + 1), hTerm2]
    _ = (k * k + 4 * (k + 1)) * s         := (Nat.add_mul (k * k) (4 * (k + 1)) s).symm
    _ = ((k + 2) * (k + 2)) * s           := by rw [hQuad]
    _ = s * ((k + 2) * (k + 2))           := Nat.mul_comm _ s
    _ = ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) := (sqMul (k + 1) (k + 2)).symm

/-- **LEMA 3 DEL BLUEPRINT (Nicómaco Escalado por 4):**
    $4 \cdot \sum_{k=0}^n k^3 = \big(n(n+1)\big)^2$. -/
theorem four_mul_sumCubes (n : Nat) :
    4 * sumCubes n = (n * (n + 1)) * (n * (n + 1)) := by
  induction n with
  | zero => rfl
  | succ k ih =>
    calc
      4 * sumCubes (k + 1)
        = 4 * sumCubes k + 4 * ((k + 1) * (k + 1) * (k + 1)) := Nat.mul_add 4 _ _
      _ = (k * (k + 1)) * (k * (k + 1)) + 4 * ((k + 1) * (k + 1) * (k + 1)) := by rw [ih]
      _ = ((k + 1) * (k + 2)) * ((k + 1) * (k + 2)) := nicomachus_algebraic_step k

/-- **TEOREMA FINAL DE NICÓMACO (`nicomachus_theorem`):**
    $$\sum_{k=0}^n k^3 = \left(\sum_{k=0}^n k\right)^2.$$ -/
theorem nicomachus_theorem (n : Nat) :
    sumCubes n = sumN n * sumN n := by
  -- Basta demostrar que `4 * sumCubes n = 4 * (sumN n * sumN n)` y cancelar el factor `4 > 0`!
  suffices h4 : 4 * sumCubes n = 4 * (sumN n * sumN n) by
    omega
  have hGauss := two_mul_sumN n
  have hFour : 4 * (sumN n * sumN n) = (2 * sumN n) * (2 * sumN n) := by
    change (2 * 2) * (sumN n * sumN n) = (2 * sumN n) * (2 * sumN n)
    rw [Nat.mul_assoc 2 2 (sumN n * sumN n), ← Nat.mul_assoc 2 (sumN n) (sumN n),
        Nat.mul_comm (2 * sumN n) (sumN n), ← Nat.mul_assoc 2 (sumN n) (2 * sumN n)]
  rw [four_mul_sumCubes n, hFour, hGauss]

/-! ## Estudio de Caso 2: Generalización de Hipótesis Inductivas (`generalizing acc`) -/

/-- Inversión recursiva de cola $O(n)$ con acumulador `acc`: -/
def revAcc {α : Type} : List α → List α → List α
  | [],      acc => acc
  | x :: xs, acc => revAcc xs (x :: acc)

def fastRev {α : Type} (xs : List α) : List α :=
  revAcc xs []

/-- **INVARIANTE GENERALIZADO (`revAcc_eq_reverse_append`):**
    Si intentáramos probar `revAcc xs [] = xs.reverse` por inducción directa sin generalizar `[]`,
    el caso `x :: xs` pediría probar `revAcc xs [x] = ...`, pero nuestra hipótesis inductiva solo
    hablaría de `[]`! Con `induction xs generalizing acc`, `ih` vale para **todo** `acc`. -/
theorem revAcc_eq_reverse_append {α : Type} (xs acc : List α) :
    revAcc xs acc = xs.reverse ++ acc := by
  induction xs generalizing acc with
  | nil =>
    simp [revAcc]
  | cons x rest ih =>
    calc
      revAcc (x :: rest) acc
        = revAcc rest (x :: acc)          := rfl
      _ = rest.reverse ++ (x :: acc)      := ih (x :: acc)
      _ = (rest.reverse ++ [x]) ++ acc    := by simp [List.append_assoc]
      _ = (x :: rest).reverse ++ acc      := by simp [List.reverse_cons]

/-- Especialización inmediata en 2 líneas para `acc = []`: -/
theorem fastRev_eq_reverse {α : Type} (xs : List α) :
    fastRev xs = xs.reverse := by
  dsimp [fastRev]
  rw [revAcc_eq_reverse_append, List.append_nil]

/-! ## Estudio de Caso 3: Auditoría Anti-Vacuidad (*Spec-Audit* para Agentes de IA)

Un riesgo clásico al pedir a una IA que formalice y demuestre $\forall x,\, P(x) \to Q(x)$ es que
defina accidentalmente $P(x)$ con una contradicción oculta ($P(x) \equiv \text{False}$), haciendo que
el teorema compile por explosión lógica (`False.elim`) sin probar nada real!
La defensa formal consiste en exigir siempre un **Teorema de No-Vacuidad (`Satisfiable`)**: -/

structure SafeTransferSpec where
  senderBal   : Nat
  receiverBal : Nat
  amount      : Nat

abbrev ValidTransfer (tx : SafeTransferSpec) : Prop :=
  0 < tx.amount ∧ tx.amount ≤ tx.senderBal

def executeTransfer (tx : SafeTransferSpec) : Nat × Nat :=
  (tx.senderBal - tx.amount, tx.receiverBal + tx.amount)

/-- 1. Teorema principal de conservación de fondos bajo `ValidTransfer`: -/
theorem executeTransfer_conserves_total (tx : SafeTransferSpec) (hValid : ValidTransfer tx) :
    let (s', r') := executeTransfer tx
    s' + r' = tx.senderBal + tx.receiverBal := by
  dsimp [executeTransfer, ValidTransfer] at *
  omega

/-- 2. Certificado obligatorio de **No-Vacuidad** (*Spec-Audit*): existe al menos una transacción
    concreta que satisface `ValidTransfer`, garantizando que la precondición no es contradictoria! -/
theorem validTransfer_non_vacuous : ∃ tx : SafeTransferSpec, ValidTransfer tx :=
  ⟨⟨100, 50, 25⟩, by decide⟩

-- Verificación computacional rápida: sumCubes 10 = 3025 = 55 * 55
#eval (sumCubes 10, sumN 10 * sumN 10)
#eval fastRev [1, 2, 3, 4, 5]

end LeanTT.M81
