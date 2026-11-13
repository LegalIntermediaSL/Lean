/-!
# Módulo 37: Flujos Infinitos (`Stream`), Sistemas Reactivos y Bisimulación
## Ámbito: Coinducción, Procesamiento de Señales y Sistemas de Tiempo Discreto

Mientras que los tipos inductivos como `List α` modelan secuencias **finitas** construidas desde
la base `nil`, los **tipos coinductivos** como `Stream α` modelan flujos **infinitos** de datos
definidos por sus observaciones (`head` y `tail`).
En una teoría de tipos con funciones totales, el tipo coinductivo de los flujos infinitos es
isomorfo al espacio de funciones desde los naturales: `Stream α := Nat → α`.
-/

namespace LeanTT.M37

universe u v

/-- Un flujo infinito de elementos de tipo `α` indexado por el instante de tiempo `t : Nat` -/
def StreamInf (α : Type u) : Type u :=
  Nat → α

namespace StreamInf

/-- Observación de la cabeza (instante `t = 0`) -/
def head {α : Type u} (s : StreamInf α) : α :=
  s 0

/-- Observación de la cola (desplazamiento temporal `t ↦ t + 1`) -/
def tail {α : Type u} (s : StreamInf α) : StreamInf α :=
  fun n => s (n + 1)

/-- Constructor `cons` que antepone un elemento `x` al inicio de un flujo infinito `s` -/
def cons {α : Type u} (x : α) (s : StreamInf α) : StreamInf α
  | 0     => x
  | n + 1 => s n

/-- Flujo constante `const x = (x, x, x, ...)` -/
def const {α : Type u} (x : α) : StreamInf α :=
  fun _ => x

/-- Aplicación punto a punto (`map`) sobre un flujo infinito -/
def map {α : Type u} {β : Type v} (f : α → β) (s : StreamInf α) : StreamInf β :=
  fun n => f (s n)

/-- Combinación sincrónica de dos flujos (`zipWith`) -/
def zipWith {α β γ : Type u} (f : α → β → γ) (s1 : StreamInf α) (s2 : StreamInf β) : StreamInf γ :=
  fun n => f (s1 n) (s2 n)

/-- Toma un prefijo finito de longitud `k` para inspección -/
def take {α : Type u} : Nat → StreamInf α → List α
  | 0,     _ => []
  | k + 1, s => s.head :: take k s.tail

/-! ## Leyes Coinductivas y Reconstrucción η de Streams -/

@[simp]
theorem head_cons {α : Type u} (x : α) (s : StreamInf α) :
    (cons x s).head = x := rfl

@[simp]
theorem tail_cons {α : Type u} (x : α) (s : StreamInf α) :
    (cons x s).tail = s := rfl

/-- Ley de desplegado universal de un Stream (`cons s.head s.tail = s`) -/
theorem cons_head_tail {α : Type u} (s : StreamInf α) :
    cons s.head s.tail = s := by
  funext n
  cases n <;> rfl

/-- `tail` conmuta con `map`: observar la cola después de mapear es igual a mapear la cola -/
theorem tail_map {α : Type u} {β : Type v} (f : α → β) (s : StreamInf α) :
    (s.map f).tail = s.tail.map f :=
  rfl

end StreamInf
end LeanTT.M37
