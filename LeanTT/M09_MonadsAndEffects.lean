/-!
# Módulo 09: Mónadas, Demostración de Leyes Monádicas (`LawfulMonad`) y Efectos
Guía teórica asociada: `docs/09_monadas_y_programacion_funcional.md`

En este módulo exploramos:
1. Creación desde cero de una mónada personalizada (`TrazaM ω α`, la mónada Writer)
   y demostración formal de sus leyes `LawfulFunctor`, `LawfulApplicative` y `LawfulMonad`.
2. Uso de `StateM` y `ExceptT` con notación imperativa `do`.
3. Verificación formal de programas escritos con sintaxis `do`.
-/

namespace LeanTT.M09

universe u

/-! ## 1. Construcción y Verificación Formal de una Mónada: `WriterNat` -/

/-- Una computación `WriterNat α` produce un valor de tipo `α` junto con un coste
    acumulado (un número natural `cost : Nat`). -/
structure WriterNat (α : Type u) where
  val  : α
  cost : Nat
  deriving Repr, DecidableEq

namespace WriterNat

def pure (a : α) : WriterNat α :=
  ⟨a, 0⟩

def bind (ma : WriterNat α) (f : α → WriterNat β) : WriterNat β :=
  let mb := f ma.val
  ⟨mb.val, ma.cost + mb.cost⟩

def map (f : α → β) (ma : WriterNat α) : WriterNat β :=
  ⟨f ma.val, ma.cost⟩

/-- Registra un coste adicional `c` en la computación -/
def tick (c : Nat) : WriterNat Unit :=
  ⟨(), c⟩

instance : Monad WriterNat where
  pure := WriterNat.pure
  bind := WriterNat.bind
  map  := WriterNat.map

/-- Demostración formal de que `WriterNat` satisface las leyes de los funtores y las mónadas.
    ¡En Lean 4 las leyes monádicas son teoremas verificados por el kernel! -/
instance : LawfulMonad WriterNat :=
  LawfulMonad.mk'
    (id_map := fun x => by cases x; rfl)
    (pure_bind := fun a f => by
      dsimp [Bind.bind, Pure.pure, WriterNat.bind, WriterNat.pure]
      rw [Nat.zero_add])
    (bind_assoc := fun x f g => by
      dsimp [Bind.bind, WriterNat.bind]
      rw [Nat.add_assoc])

/-- Ejemplo de programa monádico con `do` que cuenta cuántos pasos realiza -/
def collatzStep (n : Nat) : WriterNat Nat := do
  tick 1
  if n % 2 == 0 then
    return (n / 2)
  else
    return (3 * n + 1)

def tresPasosCollatz (n : Nat) : WriterNat Nat := do
  let n1 ← collatzStep n
  let n2 ← collatzStep n1
  let n3 ← collatzStep n2
  return n3

#eval tresPasosCollatz 6 -- { val := 5, cost := 3 }

/-- Teorema verificado sobre nuestro programa monádico:
    `tresPasosCollatz n` siempre consume exactamente `cost = 3` ticks para cualquier `n`. -/
theorem tresPasosCollatz_cost (n : Nat) : (tresPasosCollatz n).cost = 3 := by
  dsimp [tresPasosCollatz, collatzStep, Bind.bind, Pure.pure,
         WriterNat.bind, WriterNat.pure, tick]
  split <;> split <;> split <;> rfl

end WriterNat

/-! ## 2. Evaluador de Expresiones con Estado y Excepciones (`ExceptT` + `StateM`) -/

inductive ArithError where
  | divByZero : ArithError
  | varNotFound : String → ArithError
  deriving Repr, DecidableEq

/-- Pila de mónadas: Excepciones `ArithError` sobre un estado de memoria `List (String × Nat)` -/
abbrev EvalM := ExceptT ArithError (StateM (List (String × Nat)))

def leerVar (name : String) : EvalM Nat := do
  let env ← get
  match env.lookup name with
  | some v => return v
  | none   => throw (.varNotFound name)

def asignarVar (name : String) (val : Nat) : EvalM Unit := do
  modify (fun env => (name, val) :: env)

def divSeguraM (a b : Nat) : EvalM Nat := do
  if b == 0 then
    throw .divByZero
  else
    return (a / b)

def programaEjemplo : EvalM Nat := do
  asignarVar "x" 40
  asignarVar "y" 8
  let vx ← leerVar "x"
  let vy ← leerVar "y"
  divSeguraM vx vy

#eval (programaEjemplo.run).run [] -- (Except.ok 5, [("y", 8), ("x", 40)])

end LeanTT.M09
