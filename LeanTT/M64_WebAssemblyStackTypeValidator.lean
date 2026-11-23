/-!
# Módulo 64: Máquina Virtual Basada en Pila Tipada estilo WebAssembly (Wasm) y *Type Soundness*
## Ámbito: Máquinas Virtuales Seguras (Wasm / JVM Bytecode Verifier) y Progreso + Preservación

El estándar **WebAssembly (Wasm)** (Watt et al., PLDI 2018) consigue velocidad nativa y aislamiento
de seguridad exigiendo que todo módulo binario pase por un **Validador Estático de Pila de Tipos**
antes de ejecutarse:
- El validador simula abstractamente cada instrucción sobre una **pila de tipos (`StackTy := List WValTy`)**,
  comprobando que `i32.add` encuentra al menos dos `i32` en la cima de la pila y los reemplaza por un `i32`,
  que `i32.eq` produce un `i32` booleano, o que `i64.add` opera sobre dos `i64`.
- Si el validador acepta el bytecode, la ejecución real sobre la **pila de valores (`ValStack := List WVal`)**
  tiene garantizado matemáticamente que **jamás sufrirá un *stack underflow* ni una confusión de tipos**.

En este módulo:
1. Definimos los tipos de WebAssembly `WValTy` (`i32`, `i64`), los valores `WVal` y la relación
   de correspondencia de pila `TypedStack vs ts` (`vs.map valTy = ts`).
2. Implementamos el validador estático `typecheckInstr` y el ejecutor dinámico `execWInstr`.
3. Demostramos el **Teorema de Seguridad de Tipos de WebAssembly (`wasm_instr_type_soundness`)**:
   si `TypedStack vs ts` y `typecheckInstr ins ts = some ts'`, entonces existe una pila de valores
   resultante `vs'` tal que `execWInstr ins vs = some vs'` y `TypedStack vs' ts'`!
-/

namespace LeanTT.M64

/-- Tipos numéricos de WebAssembly -/
inductive WValTy where
  | i32 : WValTy
  | i64 : WValTy
  deriving Repr, DecidableEq

/-- Valores dinámicos en la pila de ejecución de WebAssembly -/
inductive WVal where
  | v32 : Int → WVal
  | v64 : Int → WVal
  deriving Repr, DecidableEq

/-- Extrae el tipo estático de un valor dinámico de WebAssembly -/
@[simp]
def valTy : WVal → WValTy
  | .v32 _ => .i32
  | .v64 _ => .i64

abbrev StackTy  := List WValTy
abbrev ValStack := List WVal

/-- Una pila dinámica de valores `vs` está bien tipada respecto a la pila de tipos `ts`
    si el tipo de cada valor en `vs` coincide posición a posición con `ts`. -/
def TypedStack (vs : ValStack) (ts : StackTy) : Prop :=
  vs.map valTy = ts

/-- Conjunto de instrucciones nucleares de WebAssembly -/
inductive WInstr where
  | const32 : Int → WInstr -- `i32.const n`: apila un `i32`
  | const64 : Int → WInstr -- `i64.const n`: apila un `i64`
  | add32   : WInstr       -- `i32.add`: desapila dos `i32` y apila su suma `i32`
  | add64   : WInstr       -- `i64.add`: desapila dos `i64` y apila su suma `i64`
  | dropVal : WInstr       -- `drop`: descarta el valor en la cima de la pila (polimórfico)
  deriving Repr, DecidableEq

/-- Validador estático de tipos de WebAssembly para una instrucción (`StackTy → Option StackTy`) -/
@[simp]
def typecheckInstr : WInstr → StackTy → Option StackTy
  | .const32 _, ts                 => some (.i32 :: ts)
  | .const64 _, ts                 => some (.i64 :: ts)
  | .add32,     .i32 :: .i32 :: ts => some (.i32 :: ts)
  | .add64,     .i64 :: .i64 :: ts => some (.i64 :: ts)
  | .dropVal,   _ :: ts            => some ts
  | _,          _                  => none

/-- Ejecutor dinámico de WebAssembly sobre la pila de valores (`ValStack → Option ValStack`) -/
@[simp]
def execWInstr : WInstr → ValStack → Option ValStack
  | .const32 n, vs                   => some (.v32 n :: vs)
  | .const64 n, vs                   => some (.v64 n :: vs)
  | .add32,     .v32 a :: .v32 b :: vs => some (.v32 (a + b) :: vs)
  | .add64,     .v64 a :: .v64 b :: vs => some (.v64 (a + b) :: vs)
  | .dropVal,   _ :: vs              => some vs
  | _,          _                    => none

/-! ## 1. Teorema de Seguridad de Tipos (*Type Soundness*: Progreso + Preservación) de WebAssembly -/

/-- TEOREMA CUMBRE (`wasm_instr_type_soundness`):
    Si una pila de ejecución `vs` tiene tipo `ts` (`TypedStack vs ts`) y el validador estático de Wasm
    aprueba la instrucción `ins` produciendo el nuevo tipo de pila `ts'` (`typecheckInstr ins ts = some ts'`),
    entonces:
    1. **Progreso (Ausencia de *Stack Underflow* y de Fallo de Tipo):** `execWInstr ins vs` NO devuelve `none`,
       sino `some vs'`.
    2. **Preservación:** La nueva pila de valores `vs'` tiene exactamente el tipo `ts'` (`TypedStack vs' ts'`). -/
theorem wasm_instr_type_soundness (ins : WInstr) (vs : ValStack) (ts ts' : StackTy)
    (hTyped : TypedStack vs ts)
    (hCheck : typecheckInstr ins ts = some ts') :
    ∃ vs' : ValStack, execWInstr ins vs = some vs' ∧ TypedStack vs' ts' := by
  subst hTyped
  cases ins with
  | const32 n =>
    simp only [typecheckInstr, Option.some.injEq] at hCheck
    subst hCheck
    exact ⟨.v32 n :: vs, rfl, rfl⟩
  | const64 n =>
    simp only [typecheckInstr, Option.some.injEq] at hCheck
    subst hCheck
    exact ⟨.v64 n :: vs, rfl, rfl⟩
  | dropVal =>
    cases vs with
    | nil =>
      simp [typecheckInstr] at hCheck
    | cons v rest =>
      simp only [List.map, typecheckInstr, Option.some.injEq] at hCheck
      subst hCheck
      exact ⟨rest, rfl, rfl⟩
  | add32 =>
    cases vs with
    | nil => simp [typecheckInstr] at hCheck
    | cons v1 rest1 =>
      cases rest1 with
      | nil =>
        cases v1 <;> simp [typecheckInstr] at hCheck
      | cons v2 rest2 =>
        cases v1 <;> cases v2 <;> simp [typecheckInstr] at hCheck
        next a b =>
          subst hCheck
          exact ⟨.v32 (a + b) :: rest2, rfl, rfl⟩
  | add64 =>
    cases vs with
    | nil => simp [typecheckInstr] at hCheck
    | cons v1 rest1 =>
      cases rest1 with
      | nil =>
        cases v1 <;> simp [typecheckInstr] at hCheck
      | cons v2 rest2 =>
        cases v1 <;> cases v2 <;> simp [typecheckInstr] at hCheck
        next a b =>
          subst hCheck
          exact ⟨.v64 (a + b) :: rest2, rfl, rfl⟩

end LeanTT.M64
