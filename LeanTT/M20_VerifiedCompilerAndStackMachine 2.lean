/-!
# Módulo 20: Compilador Formalmente Verificado y Máquina Virtual de Pila
## Ámbito: Compiladores Verificados (Teorema de McCarthy-Painter / CompCert en Miniatura)

Uno de los ámbitos estrella de los asistentes de demostraciones (como el compilador C
verificado **CompCert** o **evm-asm**) es demostrar que un **compilador preserva la semántica**:
el bytecode generado al compilar un programa fuente produce siempre exactamente el mismo
resultado que el intérprete de referencia del lenguaje fuente.

En este módulo:
1. Definimos un lenguaje fuente de expresiones aritméticas `ArithExpr` y su semántica `eval`.
2. Definimos una máquina virtual de pila con instrucciones `Instr` (`push`, `add`, `mul`).
3. Escribimos un compilador `compile : ArithExpr → List Instr`.
4. **Demostramos formalmente para todo programa `e` y toda pila inicial `s`** que:
   `exec (compile e) s = some (eval e :: s)`
   (¡Es decir, el código compilado jamás sufre subdesbordamiento de pila y deja `eval e` en la cima!).
-/

namespace LeanTT.M20

/-! ## 1. Lenguaje Fuente y Semántica de Referencia -/

inductive ArithExpr where
  | lit : Nat → ArithExpr
  | add : ArithExpr → ArithExpr → ArithExpr
  | mul : ArithExpr → ArithExpr → ArithExpr
  deriving Repr, DecidableEq

@[simp]
def eval : ArithExpr → Nat
  | .lit n     => n
  | .add e1 e2 => eval e1 + eval e2
  | .mul e1 e2 => eval e1 * eval e2

/-! ## 2. Lenguaje Objeto (Bytecode de Máquina de Pila) -/

inductive Instr where
  | push : Nat → Instr
  | add  : Instr
  | mul  : Instr
  deriving Repr, DecidableEq

abbrev Stack := List Nat
abbrev Code  := List Instr

/-- Ejecución de una instrucción sobre la pila (devuelve `none` si hay *Stack Underflow*) -/
@[simp]
def stepInstr (i : Instr) (s : Stack) : Option Stack :=
  match i, s with
  | .push n, s           => some (n :: s)
  | .add,    b :: a :: s => some ((a + b) :: s)
  | .mul,    b :: a :: s => some ((a * b) :: s)
  | _,       _           => none

/-- Ejecución de una secuencia de instrucciones `Code` -/
@[simp]
def exec : Code → Stack → Option Stack
  | [],      s => some s
  | i :: is, s =>
    match stepInstr i s with
    | some s' => exec is s'
    | none    => none

/-! ## 3. El Compilador `compile : ArithExpr → Code` -/

@[simp]
def compile : ArithExpr → Code
  | .lit n     => [.push n]
  | .add e1 e2 => compile e1 ++ compile e2 ++ [.add]
  | .mul e1 e2 => compile e1 ++ compile e2 ++ [.mul]

-- Ejemplo: Compilar `(3 + 4) * 5`
def exprEjemplo : ArithExpr := .mul (.add (.lit 3) (.lit 4)) (.lit 5)
#eval compile exprEjemplo -- [push 3, push 4, add, push 5, mul]
#eval exec (compile exprEjemplo) [] -- some [35]

/-! ## 4. Demostración Formal de Corrección del Compilador -/

/-- Lema de secuenciación para `exec` sobre la concatenación de bloques de código `c1 ++ c2` -/
@[simp]
theorem exec_append (c1 c2 : Code) (s : Stack) :
    exec (c1 ++ c2) s = (exec c1 s).bind (exec c2) := by
  induction c1 generalizing s with
  | nil          => rfl
  | cons i is ih =>
    dsimp [exec]
    cases stepInstr i s with
    | none    => rfl
    | some s' => exact ih s'

/-- Lema generalizado con continuación de código `c`:
    Ejecutar `compile e ++ c` sobre `s` es idéntico a ejecutar `c` sobre `eval e :: s`. -/
theorem compile_correct_aux (e : ArithExpr) (c : Code) (s : Stack) :
    exec (compile e ++ c) s = exec c (eval e :: s) := by
  induction e generalizing c s with
  | lit n =>
    rfl
  | add e1 e2 ih1 ih2 =>
    dsimp [compile, eval]
    rw [List.append_assoc, List.append_assoc]
    rw [ih1]
    rw [← List.append_assoc]
    rw [ih2]
    rfl
  | mul e1 e2 ih1 ih2 =>
    dsimp [compile, eval]
    rw [List.append_assoc, List.append_assoc]
    rw [ih1]
    rw [← List.append_assoc]
    rw [ih2]
    rfl

/-- TEOREMA PRINCIPAL DE CORRECCIÓN DEL COMPILADOR:
    Para toda expresión `e` y toda pila `s`, ejecutar `compile e` termina sin error
    y deposita `eval e` en la cima de `s`. -/
theorem compile_correct (e : ArithExpr) (s : Stack) :
    exec (compile e) s = some (eval e :: s) := by
  have h := compile_correct_aux e [] s
  rw [List.append_nil] at h
  exact h

end LeanTT.M20
