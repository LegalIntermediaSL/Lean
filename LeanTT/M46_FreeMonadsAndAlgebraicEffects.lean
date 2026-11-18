/-!
# Módulo 46: Mónadas Libres (`Free Monad`) y Manejadores de Efectos Algebraicos
## Ámbito: Semántica Denotacional de Efectos, Intérpretes Puros y Arquitectura Funcional

Los **Efectos Algebraicos y Manejadores (*Algebraic Effects and Handlers*)** (Plotkin & Power, 2002;
Plotkin & Pretnar, 2009) separan radicalmente:
1. La **sintaxis del programa efectual**, representada como un árbol de operaciones pendientes
   (una **Mónada Libre** `KVProg α`).
2. La **semántica o interpretación (`Handler`)**, que recorre el árbol de sintaxis traduciéndolo
   a estado en memoria, trazas de auditoría o mocks de prueba.

En este módulo:
1. Construimos la mónada libre `KVProg α` para un almacén Clave-Valor (`get` y `put`).
2. Demostramos las **3 Leyes de Mónada** (`bind_pure_left`, `bind_pure_right`, `bind_assoc`)
   por inducción estructural sobre el árbol de sintaxis.
3. Implementamos un manejador de estado puro `handleState` y **demostramos formalmente las leyes
   ecuacionales de un almacén Clave-Valor** (*Read-After-Write* y homomorfismo de `bind`).
-/

namespace LeanTT.M46

universe u v

/-- Árbol sintáctico de un programa con efectos algebraicos de lectura (`get`) y escritura (`put`)
    sobre un almacén Clave-Valor `String → Int`. -/
inductive KVProg (α : Type u) : Type u where
  | pure : α → KVProg α
  | get  : String → (Int → KVProg α) → KVProg α
  | put  : String → Int → KVProg α → KVProg α

namespace KVProg

/-- Composición secuencial (`bind` / `>>=`) de árboles de efectos injertando la continuación `k`
    en cada hoja `.pure a`. -/
@[simp]
def bind {α : Type u} {β : Type v} : KVProg α → (α → KVProg β) → KVProg β
  | .pure a,      k => k a
  | .get key c,   k => .get key (fun v => bind (c v) k)
  | .put key v p, k => .put key v (bind p k)

/-- Constructores auxiliares ergonómicos para escribir programas en estilo monádico -/
def readKey (key : String) : KVProg Int :=
  .get key .pure

def writeKey (key : String) (val : Int) : KVProg Unit :=
  .put key val (.pure ())

/-! ## 1. Demostración de las 3 Leyes Monádicas de la Mónada Libre `KVProg` -/

/-- Ley 1 (Identidad Izquierda): `bind (pure a) k = k a` -/
@[simp]
theorem bind_pure_left {α : Type u} {β : Type v} (a : α) (k : α → KVProg β) :
    bind (.pure a) k = k a :=
  rfl

/-- Ley 2 (Identidad Derecha): `bind p pure = p` -/
@[simp]
theorem bind_pure_right {α : Type u} (p : KVProg α) :
    bind p .pure = p := by
  induction p with
  | pure a          => rfl
  | get key c ih    =>
    dsimp [bind]
    congr 1
    funext v
    exact ih v
  | put key v q ih  =>
    dsimp [bind]
    rw [ih]

/-- Ley 3 (Asociatividad): `bind (bind p f) g = bind p (fun x => bind (f x) g)` -/
theorem bind_assoc {α β γ : Type u} (p : KVProg α) (f : α → KVProg β) (g : β → KVProg γ) :
    bind (bind p f) g = bind p (fun x => bind (f x) g) := by
  induction p with
  | pure a          => rfl
  | get key c ih    =>
    dsimp [bind]
    congr 1
    funext v
    exact ih v
  | put key v q ih  =>
    dsimp [bind]
    rw [ih]

/-! ## 2. Manejador de Efectos (`handleState`) y Leyes Algebraicas de Estado -/

abbrev Store := String → Int

def updateStore (st : Store) (k : String) (v : Int) : Store :=
  fun x => if x = k then v else st x

/-- Intérprete (Manejador de Efectos) que evalúa `KVProg α` sobre un estado funcional `Store` -/
@[simp]
def handleState {α : Type u} (st : Store) : KVProg α → α × Store
  | .pure a       => (a, st)
  | .get key c    => handleState st (c (st key))
  | .put key v p  => handleState (updateStore st key v) p

/-- LEY ALGEBRAICA 1 (*Read-After-Write*):
    Escribir el valor `v` en la clave `k` y leer inmediatamente la misma clave `k`
    devuelve siempre el valor `v` recién escrito! -/
theorem handler_read_after_write (st : Store) (k : String) (v : Int) :
    (handleState st (.put k v (.get k .pure))).1 = v := by
  simp [handleState, updateStore]

/-- LEY ALGEBRAICA 2 (*Homomorfismo del Manejador respecto a `bind`*):
    Ejecutar `handleState` sobre `bind p k` equivale a ejecutar `p` y pasar el valor y el
    estado resultante a `k`. -/
theorem handleState_bind {α β : Type u} (st : Store) (p : KVProg α) (k : α → KVProg β) :
    handleState st (bind p k) =
      let res := handleState st p
      handleState res.2 (k res.1) := by
  induction p generalizing st with
  | pure a         => rfl
  | get key c ih   => exact ih (st key) st
  | put key v q ih => exact ih (updateStore st key v)

end KVProg
end LeanTT.M46
