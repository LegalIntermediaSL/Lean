/-!
# Módulo 05: Familias Inductivas Indexadas, Eliminadores y Recursión Bien Fundada
Guía teórica asociada: `docs/05_familias_inductivas_y_recursividad.md`

En este módulo exploramos:
1. Familias inductivas indexadas en `Prop` (el predicado inductivo `EsPar : Nat → Prop`).
2. Familias inductivas indexadas en `Type`: Vectores `Vec α n` y ordinales finitos `Fin' n`.
3. Indexación segura `Vec.get : Vec α n → Fin' n → α` sin comprobaciones dinámicas.
4. Uso explícito de eliminadores (`Nat.rec`) para entender cómo compila Lean.
5. Recursión bien fundada (`termination_by`) en algoritmos no estructurales.
-/

namespace LeanTT.M05

universe u

/-! ## 1. Predicados Inductivos Indexados (`EsPar : Nat → Prop`) -/

/-- Definición inductiva de cuándo un número natural es par -/
inductive EsPar : Nat → Prop where
  | zero : EsPar 0
  | step : {n : Nat} → EsPar n → EsPar (n + 2)

/-- Prueba constructiva de que 6 es par -/
theorem seis_es_par : EsPar 6 :=
  EsPar.step (EsPar.step (EsPar.step EsPar.zero))

/-- Inversión de constructores: como 1 no unifica ni con `0` ni con `n + 2`,
    Lean demuestra que `¬ EsPar 1` directamente por análisis de casos (`nomatch`). -/
theorem uno_no_es_par : ¬ EsPar 1 :=
  fun h => nomatch h

/-- La suma de dos números pares es par (inducción sobre la derivación `EsPar m`) -/
theorem suma_es_par {m n : Nat} (hm : EsPar m) (hn : EsPar n) : EsPar (m + n) := by
  induction hm with
  | zero =>
    rw [Nat.zero_add]
    exact hn
  | step _ ih =>
    rw [Nat.add_right_comm]
    exact EsPar.step ih

/-! ## 2. Familias Inductivas en `Type`: Ordinales Finitos `Fin' n` y Vectores `Vec α n` -/

/-- `Fin' n` es el tipo canónico con exactamente `n` elementos (`0, 1, ..., n - 1`).
    En particular, `Fin' 0` es isomorfo a `Empty` (no tiene constructores). -/
inductive Fin' : Nat → Type where
  | fzero : {n : Nat} → Fin' (n + 1)
  | fsucc : {n : Nat} → Fin' n → Fin' (n + 1)
  deriving Repr

/-- Vectores de longitud estática `n` -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n + 1)
  deriving Repr

namespace Vec

/-- `head` seguro en tiempo de compilación: solo acepta vectores de longitud `n + 1` -/
def head {α : Type u} {n : Nat} : Vec α (n + 1) → α
  | cons x _ => x

/-- `tail` seguro en tiempo de compilación -/
def tail {α : Type u} {n : Nat} : Vec α (n + 1) → Vec α n
  | cons _ xs => xs

/-- Acceso por índice 100% libre de errores de fuera de rango (`OutOfBounds`):
    dado un vector de longitud `n` y un índice `i : Fin' n`, siempre devuelve un `α`. -/
def get {α : Type u} {n : Nat} : Vec α n → Fin' n → α
  | cons x _,  Fin'.fzero   => x
  | cons _ xs, Fin'.fsucc i => get xs i

/-- Mapa funcional que preserva estáticamente la longitud `n` del vector -/
def map {α β : Type u} {n : Nat} (f : α → β) : Vec α n → Vec β n
  | nil       => nil
  | cons x xs => cons (f x) (map f xs)

/-- Teorema funtorial sobre vectores demostrado por inducción estructural sobre `v` -/
theorem map_id {α : Type u} {n : Nat} (v : Vec α n) : map (fun x => x) v = v := by
  induction v with
  | nil          => rfl
  | cons _ _ ih  => simp [map, ih]

end Vec

/-! ## 3. Uso Explícito del Eliminador `Nat.rec` sin `match` -/

/-- Definición de `doble` invocando directamente el eliminador primitivo `Nat.rec` -/
def dobleConRec (n : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat)
    0
    (fun _ recVal => recVal + 2)
    n

#eval dobleConRec 7 -- 14

/-! ## 4. Recursión Bien Fundada (`termination_by`) -/

/-- Números de Fibonacci con acumulador en tiempo lineal `O(n)` -/
def fibFast (n : Nat) : Nat :=
  loop n 0 1
where
  loop : Nat → Nat → Nat → Nat
    | 0,     a, _ => a
    | k + 1, a, b => loop k b (a + b)

#eval fibFast 20 -- 6765

/-- División entera por restas sucesivas usando recursión bien fundada (`termination_by`) -/
def divRestas (a b : Nat) (hb : 0 < b) : Nat :=
  if h : a < b then
    0
  else
    have : a - b < a := Nat.sub_lt (Nat.lt_of_lt_of_le hb (Nat.not_lt.mp h)) hb
    1 + divRestas (a - b) b hb
termination_by a

#eval divRestas 17 5 (by decide) -- 3

end LeanTT.M05
