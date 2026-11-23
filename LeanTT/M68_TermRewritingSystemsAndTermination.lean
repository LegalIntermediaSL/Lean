/-!
# Módulo 68: Sistemas de Reescritura de Términos (TRS) e Interpretaciones Polinómicas de Terminación
## Ámbito: Álgebra Computacional, Reescritura de Términos (Baader & Nipkow) y Pruebas de Terminación

Un problema clásico en teoría de compiladores y demostradores automáticos es probar que un
**Sistema de Reescritura de Términos (TRS)** termina siempre (*Strong Normalization*), incluso cuando
las reglas de reescritura **duplican subtérminos y hacen crecer el tamaño sintáctico del árbol**.

El ejemplo canónico es la regla de distribución de la multiplicación sobre la suma:
$$x \cdot (y + z) \;\longrightarrow\; (x \cdot y) + (x \cdot z)$$
Observa que el término derecho tiene **más nodos** ($5$ nodos) que el término izquierdo ($3$ nodos)
y duplica el subtérmino $x$ (que puede ser gigantesco). ¿Por qué termina siempre esta regla?

En 1979, **Dallas Lankford** introdujo las **Interpretaciones Polinómicas de Terminación**:
asignamos a cada constructor un polinomio monótono sobre $\mathbb{N}_{\ge 2}$:
- $\llbracket \text{var } i \rrbracket = 2$
- $\llbracket A + B \rrbracket = \llbracket A \rrbracket + \llbracket B \rrbracket + 1$
- $\llbracket A \cdot B \rrbracket = \llbracket A \rrbracket \cdot \llbracket B \rrbracket$

En este módulo:
1. Formalizamos términos algebraicos `RingExpr`, su tamaño sintáctico `nodeCount` y la interpretación
   polinómica de Lankford `polyNorm`.
2. Demostramos que todo término tiene norma polinómica $\ge 2$ (`two_le_polyNorm`).
3. Demostramos el **Teorema de Decrecimiento Estricto de Lankford (`polyNorm_distrib_left_lt` y `polyNorm_distrib_right_lt`)**:
   aplicar la regla distributiva $A \cdot (B + C) \longrightarrow (A \cdot B) + (A \cdot C)$ **disminuye estrictamente**
   `polyNorm`, garantizando que cualquier secuencia de expansiones distributivas termina en un número finito de pasos!
-/

namespace LeanTT.M68

/-- Términos algebraicos construidos con variables, suma y producto -/
inductive RingExpr where
  | var : Nat → RingExpr
  | add : RingExpr → RingExpr → RingExpr
  | mul : RingExpr → RingExpr → RingExpr
  deriving Repr, DecidableEq

/-- Interpretación Polinómica de Lankford (`polyNorm : RingExpr → Nat`):
    - Cada hoja `.var _` vale `2`.
    - La suma `.add a b` vale `polyNorm a + polyNorm b + 1`.
    - El producto `.mul a b` vale `polyNorm a * polyNorm b`. -/
@[simp]
def polyNorm : RingExpr → Nat
  | .var _   => 2
  | .add a b => polyNorm a + polyNorm b + 1
  | .mul a b => polyNorm a * polyNorm b

/-! ## 1. Cota Inferior Universal de la Norma Polinómica (`polyNorm e ≥ 2`) -/

/-- Lema aritmético auxiliar: si `a ≥ 2` y `b ≥ 2`, entonces `a * b ≥ 2` (de hecho `≥ 4`). -/
theorem two_le_mul_of_two_le {a b : Nat} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    2 ≤ a * b := by
  have h1 : 2 * 2 ≤ a * b := Nat.mul_le_mul ha hb
  omega

/-- TEOREMA 1: Todo término `e : RingExpr` tiene norma polinómica `polyNorm e ≥ 2`. -/
theorem two_le_polyNorm (e : RingExpr) : 2 ≤ polyNorm e := by
  induction e with
  | var _ =>
    dsimp [polyNorm]
    omega
  | add a b iha ihb =>
    dsimp [polyNorm]
    omega
  | mul a b iha ihb =>
    dsimp [polyNorm]
    exact two_le_mul_of_two_le iha ihb

/-! ## 2. Teorema de Terminación de Lankford para las Reglas Distributivas -/

/-- TEOREMA 2 (Decrecimiento Estricto de la Distribución por la Izquierda):
    Para cualesquiera subtérminos `a, b, c : RingExpr`, el término reescrito `(a · b) + (a · c)`
    tiene una norma polinómica **estrictamente menor** que el término original `a · (b + c)`:
    `polyNorm (.add (.mul a b) (.mul a c)) < polyNorm (.mul a (.add b c))`!
    Demostración algebraica:
    - Lado izquierdo: `A * B + A * C + 1`
    - Lado derecho:  `A * (B + C + 1) = A * B + A * C + A`
    - Como `A = polyNorm a ≥ 2 > 1`, el lado derecho supera estrictamente al izquierdo! -/
theorem polyNorm_distrib_left_strict_decrease (a b c : RingExpr) :
    polyNorm (.add (.mul a b) (.mul a c)) < polyNorm (.mul a (.add b c)) := by
  have ha : 2 ≤ polyNorm a := two_le_polyNorm a
  dsimp [polyNorm]
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
  omega

/-- TEOREMA 3 (Decrecimiento Estricto de la Distribución por la Derecha):
    Para cualesquiera subtérminos `a, b, c : RingExpr`, reescribir `(a + b) · c ⟶ (a · c) + (b · c)`
    también disminuye estrictamente `polyNorm`! -/
theorem polyNorm_distrib_right_strict_decrease (a b c : RingExpr) :
    polyNorm (.add (.mul a c) (.mul b c)) < polyNorm (.mul (.add a b) c) := by
  have hc : 2 ≤ polyNorm c := two_le_polyNorm c
  dsimp [polyNorm]
  rw [Nat.add_mul, Nat.add_mul, Nat.one_mul]
  omega

end LeanTT.M68
