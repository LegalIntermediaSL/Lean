/-!
# Módulo 38: Diferenciación Automática (*Forward-Mode AD*) Formalmente Verificada
## Ámbito: Aprendizaje Automático Verificado y Cálculo Científico (Inspirado en `SciLean`)

La **Diferenciación Automática en Modo Directo (*Forward-Mode AD*)** calcula simultáneamente el
valor de una función $f(x)$ y su derivada exacta $f'(x)$ evaluando la función sobre el anillo de
los **Números Duales** de Clifford:
$$D = \{ a + b\varepsilon \mid a, b \in \mathbb{Z},\; \varepsilon^2 = 0 \}$$

Al imponer que $\varepsilon^2 = 0$, la expansión de Taylor se trunca de forma exacta en el
primer orden: $f(x + 1\cdot\varepsilon) = f(x) + f'(x)\varepsilon$.
En este módulo definimos el álgebra de números duales, un lenguaje de expresiones polinómicas
diferenciables y **demostramos formalmente la Regla de la Suma, la Regla de Leibniz del Producto
y la Corrección del Diferenciador Automático**.
-/

namespace LeanTT.M38

/-- Un Número Dual `a + b·ε` contiene la parte real `val` y la derivada tangente `der` -/
structure Dual where
  val : Int
  der : Int
  deriving Repr, DecidableEq

namespace Dual

/-- Constante `c`: su derivada es `0` -/
@[simp]
def const (c : Int) : Dual := ⟨c, 0⟩

/-- La variable independiente `x`: evaluada con semilla tangente `1` (`x + 1·ε`) -/
@[simp]
def var (x : Int) : Dual := ⟨x, 1⟩

/-- Suma de números duales: `(a + a'ε) + (b + b'ε) = (a + b) + (a' + b')ε` -/
@[simp]
def add (u v : Dual) : Dual :=
  ⟨u.val + v.val, u.der + v.der⟩

/-- Multiplicación de números duales usando `ε² = 0` (¡Regla del Producto de Leibniz!):
    `(a + a'ε)(b + b'ε) = a·b + (a'·b + a·b')ε` -/
@[simp]
def mul (u v : Dual) : Dual :=
  ⟨u.val * v.val, u.der * v.val + u.val * v.der⟩

end Dual

/-! ## Lenguaje de Funciones Polinómicas y Comparación entre Derivada Simbólica y AD -/

inductive PolyExpr where
  | const : Int → PolyExpr
  | var   : PolyExpr
  | add   : PolyExpr → PolyExpr → PolyExpr
  | mul   : PolyExpr → PolyExpr → PolyExpr
  deriving Repr, DecidableEq

/-- Evaluación ordinaria en `Int` -/
@[simp]
def evalInt : PolyExpr → Int → Int
  | .const c,   _ => c
  | .var,       x => x
  | .add e1 e2, x => evalInt e1 x + evalInt e2 x
  | .mul e1 e2, x => evalInt e1 x * evalInt e2 x

/-- Derivada simbólica formal $\frac{d}{dx} e$ -/
@[simp]
def symbolicDiff : PolyExpr → PolyExpr
  | .const _   => .const 0
  | .var       => .const 1
  | .add e1 e2 => .add (symbolicDiff e1) (symbolicDiff e2)
  | .mul e1 e2 => .add (.mul (symbolicDiff e1) e2) (.mul e1 (symbolicDiff e2))

/-- Evaluación mediante Diferenciación Automática (`Forward-Mode AD`) sobre `Dual` -/
@[simp]
def evalDual : PolyExpr → Int → Dual
  | .const c,   _ => Dual.const c
  | .var,       x => Dual.var x
  | .add e1 e2, x => Dual.add (evalDual e1 x) (evalDual e2 x)
  | .mul e1 e2, x => Dual.mul (evalDual e1 x) (evalDual e2 x)

/-- TEOREMA FUNDAMENTAL DE LA DIFERENCIACIÓN AUTOMÁTICA:
    Para toda expresión `e : PolyExpr` y todo punto `x : Int`, `evalDual e x` calcula
    simultáneamente el valor exacto `evalInt e x` y el valor exacto de su derivada simbólica
    `evalInt (symbolicDiff e) x` en una sola pasada! -/
theorem forwardAD_correct (e : PolyExpr) (x : Int) :
    evalDual e x = ⟨evalInt e x, evalInt (symbolicDiff e) x⟩ := by
  induction e with
  | const c =>
    rfl
  | var =>
    rfl
  | add e1 e2 ih1 ih2 =>
    dsimp [evalDual, symbolicDiff, evalInt]
    rw [ih1, ih2]
  | mul e1 e2 ih1 ih2 =>
    dsimp [evalDual, symbolicDiff, evalInt]
    rw [ih1, ih2]

end LeanTT.M38
