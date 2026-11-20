/-!
# Módulo 59: Lógica de Hoare y Cálculo de la Precondición Más Débil (*Weakest Precondition*, Dijkstra `wp`)
## Ámbito: Verificación Deductiva de Programas (Estilo Dafny / Why3 / F* Dijkstra Monads)

En la verificación formal de software imperativo (Floyd-Hoare 1969, Edsger W. Dijkstra 1975),
una **Tripleta de Hoare** $\{P\}\; c\; \{Q\}$ afirma que si el comando `c` se ejecuta desde un estado
inicial que cumple la precondición `P`, el estado final resultante cumplirá la postcondición `Q`.

Para automatizar la demostración de tripletas de Hoare sin adivinar estados intermedios en
secuencias `c1 ; c2` y condicionales `if`, Dijkstra inventó el transformador de predicados
**Precondición Más Débil (`wp c Q`)**, que calcula hacia atrás la condición exacta sobre el estado
inicial para que `c` termine cumpliendo `Q`.
-/

namespace LeanTT.M59

/-- Estado de memoria con dos registros enteros `x` e `y` -/
structure State2 where
  x : Int
  y : Int
  deriving Repr, DecidableEq

/-- Expresiones aritméticas sobre el estado `(x, y)` -/
inductive AExp where
  | const : Int → AExp
  | varX  : AExp
  | varY  : AExp
  | add   : AExp → AExp → AExp
  | sub   : AExp → AExp → AExp
  deriving Repr, DecidableEq

@[simp]
def evalAExp (s : State2) : AExp → Int
  | .const n   => n
  | .varX      => s.x
  | .varY      => s.y
  | .add e1 e2 => evalAExp s e1 + evalAExp s e2
  | .sub e1 e2 => evalAExp s e1 - evalAExp s e2

/-- Comandos imperativos libres de bucles (fragmento de ejecución simbólica exacta) -/
inductive Stmt where
  | skip    : Stmt
  | assignX : AExp → Stmt
  | assignY : AExp → Stmt
  | seq     : Stmt → Stmt → Stmt
  | ifPosX  : Stmt → Stmt → Stmt
  deriving Repr, DecidableEq

/-- Semántica operacional determinista de un comando `Stmt` -/
@[simp]
def execStmt (c : Stmt) (s : State2) : State2 :=
  match c with
  | .skip       => s
  | .assignX e  => { s with x := evalAExp s e }
  | .assignY e  => { s with y := evalAExp s e }
  | .seq c1 c2  => execStmt c2 (execStmt c1 s)
  | .ifPosX t f => if s.x > 0 then execStmt t s else execStmt f s

/-- Una Tripleta de Hoare `{P} c {Q}` es válida si para todo estado inicial `s` que cumple `P s`,
    el estado final `execStmt c s` cumple la postcondición `Q`. -/
def HoareTriple (P : State2 → Prop) (c : Stmt) (Q : State2 → Prop) : Prop :=
  ∀ s : State2, P s → Q (execStmt c s)

/-! ## 1. El Transformador de Precondición Más Débil (`wp`) de Edsger W. Dijkstra -/

/-- Calcula recursivamente hacia atrás la precondición más débil `wp c Q : State2 → Prop` -/
@[simp]
def wp (c : Stmt) (Q : State2 → Prop) : State2 → Prop :=
  match c with
  | .skip       => Q
  | .assignX e  => fun s => Q { s with x := evalAExp s e }
  | .assignY e  => fun s => Q { s with y := evalAExp s e }
  | .seq c1 c2  => wp c1 (wp c2 Q)
  | .ifPosX t f => fun s => if s.x > 0 then wp t Q s else wp f Q s

/-- TEOREMA 1 (Exactitud Puntual del Transformador de Dijkstra):
    Para todo comando `c`, toda postcondición `Q` y todo estado inicial `s`,
    `wp c Q s` es exactamente equivalente a `Q (execStmt c s)`. -/
@[simp]
theorem wp_iff_execStmt (c : Stmt) (Q : State2 → Prop) (s : State2) :
    wp c Q s ↔ Q (execStmt c s) := by
  induction c generalizing Q s with
  | skip              => exact Iff.rfl
  | assignX e         => exact Iff.rfl
  | assignY e         => exact Iff.rfl
  | seq c1 c2 ih1 ih2 =>
    dsimp [wp, execStmt]
    rw [ih1, ih2]
  | ifPosX t f iht ihf =>
    dsimp [wp, execStmt]
    split
    · exact iht Q s
    · exact ihf Q s

/-- TEOREMA 2 (Corrección y Completitud de la Generación de Condiciones de Verificación `VCGen`):
    Una tripleta de Hoare `{P} c {Q}` es válida si y solo si `P` implica puntualmente `wp c Q`. -/
theorem hoareTriple_iff_imp_wp (P : State2 → Prop) (c : Stmt) (Q : State2 → Prop) :
    HoareTriple P c Q ↔ (∀ s : State2, P s → wp c Q s) := by
  constructor
  · intro h s hP
    exact (wp_iff_execStmt c Q s).mpr (h s hP)
  · intro h s hP
    exact (wp_iff_execStmt c Q s).mp (h s hP)

/-! ## 2. Caso de Estudio: Verificación del Algoritmo de Intercambio Aritmético In-Place (Sin Variable Auxiliar) -/

/-- Algoritmo clásico que intercambia `x` e `y` sin usar un tercer registro temporal:
    1. `x := x + y`
    2. `y := x - y`
    3. `x := x - y` -/
def arithSwapProg : Stmt :=
  .seq (.assignX (.add .varX .varY))
       (.seq (.assignY (.sub .varX .varY))
             (.assignX (.sub .varX .varY)))

/-- TEOREMA 3: Verificación formal mediante `wp` de que `arithSwapProg` intercambia los valores
    de cualesquiera dos enteros iniciales `x0` e `y0`! -/
theorem arithSwapProg_correct (x0 y0 : Int) :
    HoareTriple
      (fun s => s.x = x0 ∧ s.y = y0)
      arithSwapProg
      (fun s => s.x = y0 ∧ s.y = x0) := by
  rw [hoareTriple_iff_imp_wp]
  intro s ⟨hx, hy⟩
  dsimp [arithSwapProg, wp, evalAExp]
  omega

end LeanTT.M59
