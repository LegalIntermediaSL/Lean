/-!
# Módulo 52: Forma de Asignación Única Estática (SSA) y Optimización de Propagación de Constantes
## Ámbito: Diseño de Compiladores Modernos (LLVM / Lean 4 IR) y Transformaciones Verificadas

En los compiladores modernos (como LLVM o la representación intermedia `Lean.IR` de Lean 4),
el código se transforma a forma **SSA (*Static Single Assignment*)**, donde cada instrucción
asigna un valor a un registro inmutable y los programas son secuencias lineales de asignaciones.

En este módulo:
1. Modelamos instrucciones SSA (`SSAInstr`) que operan sobre operandos (`Operand`: literales o registros)
   y escriben en un banco de registros `RegFile`.
2. Implementamos una pasada de optimización de **Plegado de Constantes (*Constant Folding*)** (`foldInstr` y `foldProg`)
   que precalcula en tiempo de compilación las sumas y productos de operandos literales.
3. Demostramos formalmente que la optimización preserva la semántica exacta de cualquier
   banco de registros para cualquier programa SSA (`execProg_foldProg`).
-/

namespace LeanTT.M52

abbrev RegId := Nat
abbrev RegFile := RegId → Nat

/-- Actualización inmutable de un registro `dst` en el banco de registros `rf` -/
@[simp]
def updateReg (rf : RegFile) (dst : RegId) (val : Nat) : RegFile :=
  fun r => if r == dst then val else rf r

/-- Un operando en SSA es o bien una constante inmediata (`imm n`) o la lectura de un registro (`reg r`) -/
inductive Operand where
  | imm : Nat → Operand
  | reg : RegId → Operand
  deriving Repr, DecidableEq

/-- Evaluación de un operando en un banco de registros `rf` -/
@[simp]
def evalOp (rf : RegFile) : Operand → Nat
  | .imm n => n
  | .reg r => rf r

/-- Instrucción SSA de tres direcciones (`dst := op1 ⊕ op2` o copia `dst := op`) -/
inductive SSAInstr where
  | assign : RegId → Operand → SSAInstr
  | add    : RegId → Operand → Operand → SSAInstr
  | mul    : RegId → Operand → Operand → SSAInstr
  deriving Repr, DecidableEq

/-- Ejecución de una instrucción SSA produciendo el nuevo banco de registros -/
@[simp]
def execInstr (rf : RegFile) : SSAInstr → RegFile
  | .assign dst op   => updateReg rf dst (evalOp rf op)
  | .add dst op1 op2 => updateReg rf dst (evalOp rf op1 + evalOp rf op2)
  | .mul dst op1 op2 => updateReg rf dst (evalOp rf op1 * evalOp rf op2)

/-- Ejecución secuencial de un bloque básico SSA (`List SSAInstr`) -/
@[simp]
def execProg (rf : RegFile) : List SSAInstr → RegFile
  | []          => rf
  | ins :: rest => execProg (execInstr rf ins) rest

/-! ## 1. Pasada de Optimización: Plegado de Constantes (`Constant Folding`) -/

/-- Optimiza una instrucción SSA plegando sumas y productos de constantes inmediatas: -/
@[simp]
def foldInstr : SSAInstr → SSAInstr
  | .assign dst op =>
    .assign dst op
  | .add dst op1 op2 =>
    match op1, op2 with
    | .imm a, .imm b => .assign dst (.imm (a + b))
    | _,      _      => .add dst op1 op2
  | .mul dst op1 op2 =>
    match op1, op2 with
    | .imm a, .imm b => .assign dst (.imm (a * b))
    | _,      _      => .mul dst op1 op2

/-- Aplica la optimización de plegado de constantes a todo un bloque básico SSA -/
@[simp]
def foldProg : List SSAInstr → List SSAInstr
  | []          => []
  | ins :: rest => foldInstr ins :: foldProg rest

/-! ## 2. Verificación Formal de Preservación Semántica -/

/-- TEOREMA 1 (Corrección Local por Instrucción SSA):
    Ejecutar `foldInstr ins` produce exactamente el mismo banco de registros `RegFile`
    que ejecutar la instrucción original `ins`. -/
@[simp]
theorem execInstr_foldInstr (rf : RegFile) (ins : SSAInstr) :
    execInstr rf (foldInstr ins) = execInstr rf ins := by
  cases ins with
  | assign dst op   => rfl
  | add dst op1 op2 => cases op1 <;> cases op2 <;> rfl
  | mul dst op1 op2 => cases op1 <;> cases op2 <;> rfl

/-- TEOREMA 2 (Preservación Semántica Global del Optimizador SSA):
    Para cualquier banco de registros inicial `rf` y cualquier bloque básico `prog`,
    el programa optimizado `foldProg prog` produce exactamente el mismo estado final que `prog`. -/
theorem execProg_foldProg (rf : RegFile) (prog : List SSAInstr) :
    execProg rf (foldProg prog) = execProg rf prog := by
  induction prog generalizing rf with
  | nil =>
    rfl
  | cons ins rest ih =>
    simp only [foldProg, execProg, execInstr_foldInstr]
    exact ih (execInstr rf ins)

end LeanTT.M52
