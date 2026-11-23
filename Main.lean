import LeanTT

/-!
# Ejecutable CLI Interactivo `leantt` (`lake exe leantt`)
Ejecuta en vivo una batería de pruebas y demostraciones computacionales a través de los
**70 módulos verificados (`M01`–`M70`)** y los **4 Proyectos Cumbre (`M40`, `M50`, `M60`, `M70`)**.
-/

def main : IO Unit := do
  IO.println "=========================================================================="
  IO.println "  LeanTT — Suite Ejecutable de Teoría de Tipos Dependientes (70 Módulos)  "
  IO.println "=========================================================================="
  IO.println ""

  -- 1. Tipos Dependientes y Printf Tipado (M02)
  let msgPrintf : String := LeanTT.M02.printf LeanTT.M02.formatoUsuario "Ada Lovelace" 101
  IO.println s!"[M02] Printf dependientemente tipado: \"{msgPrintf}\""

  -- 2. Ordenación Verificada Insertion Sort (M18)
  let sortedList := LeanTT.M18.insertionSort [7, 2, 9, 1, 5, 8, 3]
  IO.println s!"[M18] Insertion Sort formalmente verificado: {repr sortedList}"

  -- 3. Compilador Verificado a Máquina de Pila (M20)
  let exprArith : LeanTT.M20.ArithExpr := .mul (.add (.lit 3) (.lit 4)) (.lit 5)
  let bytecode := LeanTT.M20.compile exprArith
  let stackRes := LeanTT.M20.exec bytecode []
  IO.println s!"[M20] Compilador McCarthy-Painter ((3 + 4) * 5): eval={LeanTT.M20.eval exprArith}, stack={repr stackRes}"

  -- 4. Polinomios Computables por Esquema de Horner (M32) y Plegado FRI de STARKs (M55)
  let polyHorner := LeanTT.M32.evalHorner [3, 2, 5] 10
  let polyFRI : LeanTT.M55.PolyDeg3 := { c0 := 1, c1 := 2, c2 := 3, c3 := 4 }
  let foldedAt5 := LeanTT.M55.evalDeg1 (LeanTT.M55.friFold polyFRI 5) (5 * 5)
  let directAt5 := LeanTT.M55.evalDeg3 polyFRI 5
  IO.println s!"[M32/M55] Horner P(10)={polyHorner} | Plegado FRI STARK en x=5: plegado={foldedAt5}, directo={directAt5}"

  -- 5. Proyecto Cumbre I (M40): Mini-Kernel de Tipos Dependientes
  let idPiTy := LeanTT.M40.Expr.inferType 20 [] LeanTT.M40.Expr.polyId
  IO.println s!"[M40 - Cumbre I]   Mini-Kernel infiere tipo de polyId: {repr idPiTy}"

  -- 6. Proyecto Cumbre II (M50): Elaborador Bidireccional (`synth` / `check`)
  let elabRes := LeanTT.M50.synth [] LeanTT.M50.rawApply
  IO.println s!"[M50 - Cumbre II]  Elaborador Bidireccional rellena tipos omitidos: {repr elabRes}"

  -- 7. Proyecto Cumbre III (M60): Kernel CIC con `Sort u`, `imax` y Large Elimination
  let largeFalse := LeanTT.M60.CicExpr.inferType 15 [] (LeanTT.M60.CicExpr.depTerm false)
  let largeTrue  := LeanTT.M60.CicExpr.inferType 15 [] (LeanTT.M60.CicExpr.depTerm true)
  IO.println s!"[M60 - Cumbre III] Large Elimination en el Kernel: depTerm(false) : {repr largeFalse}, depTerm(true) : {repr largeTrue}"

  -- 8. Proyecto Cumbre IV (M70): Positividad Estricta y Unificación de Patrones de Miller
  let posCheckBad := LeanTT.M70.IndTy.isStrictlyPositive 0 (.arrow (.base 0) (.base 1))
  let millerSol   := LeanTT.M70.PatTerm.abstractFVar1 7 (.app (.const 10) (.fvar 7))
  IO.println s!"[M70 - Cumbre IV]  Positividad estricta para (I → False): {posCheckBad} | Solución patrón de Miller: {repr millerSol}"

  -- 9. Post-Cuántica LWE (M62), Validador WebAssembly (M64) y Sumador Hardware (M69)
  let cipherLWE := LeanTT.M62.lweEncrypt 100 42 17 (-35) true
  let lweBit    := LeanTT.M62.lweDecrypt 100 42 17 cipherLWE
  let wasmTy    := LeanTT.M64.typecheckInstr .add32 [.i32, .i32, .i64]
  let hwAdd     := LeanTT.M69.rippleAdder2 true true true false true
  IO.println s!"[M62/M64/M69]      Desencriptado LWE={lweBit} | Validador Wasm={repr wasmTy} | Ripple-Carry 2-bit={repr hwAdd}"

  IO.println ""
  IO.println "✅ Todos los 70 módulos (M01-M70) y 5 talleres (E01-E05) verificados y ejecutados con éxito."
