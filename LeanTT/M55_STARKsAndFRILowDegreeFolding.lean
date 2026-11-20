/-!
# Módulo 55: Criptografía ZK Transparente (STARKs) y Plegado Polinómico FRI (*Fast Reed-Solomon IOP*)
## Ámbito: Pruebas de Conocimiento Cero Transparentes (zk-STARKs, Eli Ben-Sasson et al.)

En los sistemas **zk-STARK** (y en las librerías verificadas de `Verified-zkEVM` como `ArkLib`),
el protocolo **FRI (*Fast Reed-Solomon Interactive Oracle Proof of Proximity*)** demuestra que una
función comprometida corresponde a un polinomio de bajo grado $< d$ reduciendo recursivamente
el grado a la mitad en cada ronda mediante un desafío aleatorio $\alpha$.

La identidad algebraica que hace funcionar a FRI es la **descomposición par-impar**:
todo polinomio $P(X) = c_0 + c_1 X + c_2 X^2 + c_3 X^3$ se descompone únicamente como:
$$P(X) = P_{\text{even}}(X^2) + X \cdot P_{\text{odd}}(X^2)$$
donde $P_{\text{even}}(Y) = c_0 + c_2 Y$ y $P_{\text{odd}}(Y) = c_1 + c_3 Y$ tienen la mitad de grado.
Al recibir el desafío del Verificador $\alpha$, el Prover pliega $P$ en:
$$P_{\text{fold}}(\alpha, Y) = P_{\text{even}}(Y) + \alpha \cdot P_{\text{odd}}(Y)$$
-/

namespace LeanTT.M55

/-- Un polinomio de grado `< 4`: `P(X) = c0 + c1·X + c2·X² + c3·X³` -/
structure PolyDeg3 where
  c0 : Int
  c1 : Int
  c2 : Int
  c3 : Int
  deriving Repr, DecidableEq

/-- Un polinomio plegado de mitad de grado (`< 2`): `Q(Y) = a0 + a1·Y` -/
structure PolyDeg1 where
  a0 : Int
  a1 : Int
  deriving Repr, DecidableEq

/-- Evaluación de un polinomio de grado `< 4` en un punto `x : Int` -/
@[simp]
def evalDeg3 (P : PolyDeg3) (x : Int) : Int :=
  P.c0 + P.c1 * x + P.c2 * (x * x) + P.c3 * (x * x) * x

/-- Evaluación de un polinomio de grado `< 2` en un punto `y : Int` -/
@[simp]
def evalDeg1 (Q : PolyDeg1) (y : Int) : Int :=
  Q.a0 + Q.a1 * y

/-- Parte par de `P`: `P_even(Y) = c0 + c2·Y` -/
@[simp]
def evenPart (P : PolyDeg3) : PolyDeg1 :=
  { a0 := P.c0, a1 := P.c2 }

/-- Parte impar de `P`: `P_odd(Y) = c1 + c3·Y` -/
@[simp]
def oddPart (P : PolyDeg3) : PolyDeg1 :=
  { a0 := P.c1, a1 := P.c3 }

/-- Operador de Plegado Aleatorio de FRI (`friFold P α`):
    Combina linealmente la parte par y la parte impar usando el desafío `α : Int` del Verificador,
    reduciendo el número de coeficientes a la mitad! -/
@[simp]
def friFold (P : PolyDeg3) (α : Int) : PolyDeg1 :=
  { a0 := P.c0 + P.c1 * α
  , a1 := P.c2 + P.c3 * α }

/-! ## 1. Teoremas Algebraicos de Completitud del Plegado FRI -/

/-- TEOREMA 1 (Identidad de Descomposición Par-Impar de FRI):
    Para todo polinomio `P` y todo punto de evaluación `x : Int`:
    `P(x) = P_even(x²) + P_odd(x²) · x`. -/
theorem fri_even_odd_decomposition (P : PolyDeg3) (x : Int) :
    evalDeg3 P x = evalDeg1 (evenPart P) (x * x) + evalDeg1 (oddPart P) (x * x) * x := by
  dsimp [evalDeg3, evalDeg1, evenPart, oddPart]
  rw [Int.add_mul]
  omega

/-- TEOREMA 2 (Homomorfismo del Operador de Plegado FRI):
    Evaluar el polinomio plegado `friFold P α` en `y = x²` es idéntico a combinar linealmente
    las evaluaciones de `P_even(y)` y `P_odd(y)` con el desafío `α`! -/
theorem eval_friFold (P : PolyDeg3) (α y : Int) :
    evalDeg1 (friFold P α) y = evalDeg1 (evenPart P) y + evalDeg1 (oddPart P) y * α := by
  dsimp [evalDeg1, friFold, evenPart, oddPart]
  rw [Int.add_mul, Int.add_mul, Int.mul_right_comm P.c3 α y]
  omega

/-- TEOREMA 3 (Colapso de Evaluaciones en el Subgrupo Multiplicativo `{x, -x}`):
    Al sumar las evaluaciones de `P` en dos raíces cuadradas opuestas `x` y `-x`,
    los términos impares se cancelan exactamente y queda `2 · P_even(x²)`. -/
theorem fri_symmetric_sum (P : PolyDeg3) (x : Int) :
    evalDeg3 P x + evalDeg3 P (-x) = 2 * evalDeg1 (evenPart P) (x * x) := by
  dsimp [evalDeg3, evalDeg1, evenPart]
  have h_sq : (-x) * (-x) = x * x := Int.neg_mul_neg x x
  rw [h_sq, Int.mul_neg, Int.mul_neg]
  omega

/-- TEOREMA 4 (Identidad de Verificación Directa de FRI cuando `α = x`):
    Cuando el desafío `α` coincide con la coordenada `x`, el polinomio plegado de mitad de grado
    evaluado en `x²` coincide exactamente con la evaluación del polinomio original en `x`. -/
theorem friFold_at_x_eq_evalDeg3 (P : PolyDeg3) (x : Int) :
    evalDeg1 (friFold P x) (x * x) = evalDeg3 P x := by
  rw [eval_friFold, ← fri_even_odd_decomposition]

end LeanTT.M55
