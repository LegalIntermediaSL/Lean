/-!
# Módulo 32: Polinomios Computables, Esquema de Horner y Homomorfismo de Evaluación
## Ámbito: Álgebra Computacional Verificada (Inspirado en `Verified-zkEVM/CompPoly`)

En bibliotecas matemáticas clásicas como Mathlib4, los polinomios `Polynomial R` suelen definirse
usando funciones de soporte finito no computables para facilitar las pruebas abstractas.
Sin embargo, para ejecutar probadores criptográficos o sistemas algebraicos necesitamos una
representación **100% computable** (el propósito de **CompPoly**) y demostrar que las operaciones
sobre la lista de coeficientes respetan la evaluación matemática.

En este módulo:
1. Representamos un polinomio $p(X) = c_0 + c_1 X + c_2 X^2 + \dots + c_n X^n$ como `List Int`.
2. Implementamos su evaluación eficiente mediante la **Regla de Horner**:
   $c_0 + X \cdot (c_1 + X \cdot (c_2 + \dots))$.
3. Implementamos la suma de polinomios `addPoly` y el escalado `scalePoly`.
4. **Demostramos formalmente** que la evaluación es un homomorfismo lineal:
   - `evalHorner (addPoly p q) x = evalHorner p x + evalHorner q x`
   - `evalHorner (scalePoly c p) x = c * evalHorner p x`
-/

namespace LeanTT.M32

/-- Un polinomio computable `[c₀, c₁, c₂, ...]` representa `c₀ + c₁·X + c₂·X² + ...` -/
abbrev CompPoly := List Int

/-- Evaluación en tiempo lineal `O(deg p)` usando el Esquema de Horner -/
@[simp]
def evalHorner : CompPoly → Int → Int
  | [],      _ => 0
  | c :: cs, x => c + x * evalHorner cs x

-- Ejemplo: `p(X) = 3 + 2X + 5X²` evaluado en `X = 10` vale `3 + 20 + 500 = 523`:
#eval evalHorner [3, 2, 5] 10 -- 523

/-- Multiplicación de un polinomio por un escalar `k : Int` -/
@[simp]
def scalePoly (k : Int) : CompPoly → CompPoly
  | []      => []
  | c :: cs => (k * c) :: scalePoly k cs

/-- Suma de dos polinomios coeficiente a coeficiente (soportando grados distintos) -/
@[simp]
def addPoly : CompPoly → CompPoly → CompPoly
  | [],      q       => q
  | p,       []      => p
  | a :: as, b :: bs => (a + b) :: addPoly as bs

/-! ## Teoremas de Equivalencia entre Sintaxis Polinómica y Semántica de Evaluación -/

/-- TEOREMA 1: Evaluar un polinomio escalado `scalePoly k p` en `x` da `k * evalHorner p x` -/
theorem evalHorner_scalePoly (k : Int) (p : CompPoly) (x : Int) :
    evalHorner (scalePoly k p) x = k * evalHorner p x := by
  induction p with
  | nil          => simp
  | cons c cs ih =>
    dsimp [scalePoly, evalHorner]
    rw [ih]
    rw [Int.mul_add, ← Int.mul_assoc, ← Int.mul_assoc, Int.mul_comm x k]

/-- TEOREMA 2: Evaluar la suma `addPoly p q` en `x` es igual a la suma de las evaluaciones! -/
theorem evalHorner_addPoly (p q : CompPoly) (x : Int) :
    evalHorner (addPoly p q) x = evalHorner p x + evalHorner q x := by
  induction p generalizing q with
  | nil =>
    simp
  | cons a as ih =>
    cases q with
    | nil =>
      simp
    | cons b bs =>
      dsimp [addPoly, evalHorner]
      rw [ih bs]
      rw [Int.mul_add]
      omega

end LeanTT.M32
