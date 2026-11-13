# Módulo 09: Mónadas, Leyes Monádicas Verificadas y Programación Funcional en Lean 4

> **Archivo Lean ejecutable asociado:** [`LeanTT/M09_MonadsAndEffects.lean`](../LeanTT/M09_MonadsAndEffects.lean)

---

## 1. Lean 4 como Lenguaje Funcional Puro con Efectos Tipados

Como todas las funciones del cálculo lambda tipado son matemáticamente **puras** y **totales** (el mismo argumento produce siempre el mismo resultado sin efectos laterales ocultos), los efectos computacionales (estado mutable, excepciones, no-determinismo, lectura de configuración, entrada/salida) se modelan explícitamente mediante **Mónadas** ($M : \texttt{Type } u \to \texttt{Type } v$).

### La Jerarquía deConstructores de Efectos
1. **`Functor (f : Type u → Type v)`:**
   * Operación: `map : (α → β) → f α → f β` (notación `<$>`)
   * Leyes (`LawfulFunctor`): `id <$> x = x` y `(g ∘ h) <$> x = g <$> (h <$> x)`.
2. **`Applicative (f : Type u → Type v) extends Functor f`:**
   * Operaciones: `pure : α → f α` y `seq : f (α → β) → (Unit → f α) → f β` (notación `<*>`).
3. **`Monad (m : Type u → Type v) extends Applicative m`:**
   * Operación fundamental: `bind : m α → (α → m β) → m β` (notación `>>=`).

---

## 2. Las Tres Leyes Monádicas (`LawfulMonad`)

A diferencia de Haskell (donde las leyes monádicas son solo una convención informal en los comentarios), en **Lean 4** la clase `LawfulMonad m` contiene las **demostraciones formales verificadas** de las tres leyes de Kleisli:

1. **Identidad por la izquierda:**
   $$\texttt{pure } a \gg\!\!= f \;=\; f\; a$$
2. **Identidad por la derecha:**
   $$x \gg\!\!= \texttt{pure} \;=\; x$$
3. **Asociatividad de `bind`:**
   $$(x \gg\!\!= f) \gg\!\!= g \;=\; x \gg\!\!= (\lambda a \Rightarrow f\; a \gg\!\!= g)$$

---

## 3. La Notación `do` de Lean 4: Mucho más potente que Haskell

El elaborador de bloques `do` en Lean 4 desazucara código imperativo ergonómico (variables mutables locales `let mut`, bucles `for x in xs do`, retornos tempranos `if cond then return v`) hacia combinadores monádicos puros (`bind`, `ForIn.forIn`, `StateT`):

```lean
def sumaHastaPrimerNegativo (xs : List Int) : Nat := Id.run do
  let mut acc : Nat := 0
  for x in xs do
    if x < 0 then
      return acc
    acc := acc + x.toNat
  return acc
```
Como este bloque se ejecuta dentro de la mónada identidad `Id`, `sumaHastaPrimerNegativo` sigue siendo una **función matemática 100% pura** sobre la cual puedes demostrar teoremas formales.

---

## 4. El Catálogo de Mónadas y Transformadores en Lean 4

| Mónada / Transformador | Definición Subyacente | Efecto Modelado |
| :--- | :--- | :--- |
| **`Id α`** | `α` | Computación pura con sintaxis imperativa `do` |
| **`Option α`** | `none \| some α` | Parcialidad / ausencia de valor |
| **`Except ε α`** | `error ε \| ok α` | Excepciones tipadas con errores de tipo `ε` |
| **`ReaderT ρ m α`** | `ρ → m α` | Entorno o configuración de solo lectura `ρ` |
| **`StateT σ m α`** | `σ → m (α × σ)` | Estado mutable verificable de tipo `σ` |
| **`EStateM ε σ α`** | `σ → Result ε σ α` | Estado + excepciones (base de `CoreM`, `MetaM` y `IO`) |

> **Optimización del compilador de Lean 4 (Perceus / Counting Immutable Beans):** Gracias al conteo de referencias con reutilización destructiva en el sitio (*in-place mutation when reference count is 1*), cuando usas `StateM σ α` o modificas un `Array`, el código nativo generado por Lean 4 muta la memoria directamente sin copiar estructuras cuando hay una única referencia viva.
