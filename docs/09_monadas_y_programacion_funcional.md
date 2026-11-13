# Módulo 09: Mónadas, Leyes Monádicas Verificadas (`LawfulMonad`), Transformadores y Perceus

> **Archivo Lean ejecutable asociado:** [`LeanTT/M09_MonadsAndEffects.lean`](../LeanTT/M09_MonadsAndEffects.lean)

---

## Índice del Módulo
1. [De la Categoría de Tipos a los Funtores, Aplicativos y Mónadas](#1-de-la-categoría-de-tipos-a-los-funtores-aplicativos-y-mónadas)
2. [Especificación Completa de `LawfulFunctor`, `LawfulApplicative` y `LawfulMonad`](#2-especificación-completa-de-lawfulfunctor-lawfulapplicative-y-lawfulmonad)
3. [Cómo Desazucara Lean 4 la Notación `do` (`let mut`, `for`, `return`)](#3-cómo-desazucara-lean-4-la-notación-do-let-mut-for-return)
4. [Transformadores de Mónadas (`ReaderT`, `StateT`, `ExceptT`) y `MonadLift`](#4-transformadores-de-mónadas-readert-statet-exceptt-y-monadlift)
5. [Razonamiento Ecuacional sobre Programas Monádicos](#5-razonamiento-ecuacional-sobre-programas-monádicos)

---

## 1. De la Categoría de Tipos a los Funtores, Aplicativos y Mónadas

En Lean 4, la programación con efectos se estructura mediante constructores de tipos $m : \texttt{Type } u \to \texttt{Type } v$:

```lean
-- 1. Functor: permite aplicar una función pura `α → β` dentro de un contexto `f α`
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β

-- 2. Applicative: permite elevar valores puros (`pure`) y combinar efectos independientes (`seq`)
class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f

-- 3. Monad: permite que el siguiente efecto dependa del VALOR producido por el efecto anterior (`bind`)
class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v)
```

> **Conexión con la Teoría de Tipos Dependientes:** Mientras que `Applicative.seq` combina dos computaciones `f (α → β)` y `f α` cuya estructura de efectos es estática e independiente de los valores, `Monad.bind : m α → (α → m β) → m β` permite que la segunda computación `m β` **dependa dinámicamente del valor `a : α`** producido por la primera.

---

## 2. Especificación Completa de `LawfulFunctor`, `LawfulApplicative` y `LawfulMonad`

En Lean 4, el cumplimiento de las leyes algebraicas de un funtor o una mónada se captura mediante clases proposicionales dedicadas:

```lean
class LawfulFunctor (f : Type u → Type v) [Functor f] : Prop where
  map_const : (Functor.mapConst : α → f β → f α) = Functor.map ∘ Function.const β
  id_map    : ∀ (x : f α), id <$> x = x
  comp_map  : ∀ (g : α → β) (h : β → γ) (x : f α), (h ∘ g) <$> x = h <$> g <$> x

class LawfulMonad (m : Type u → Type v) [Monad m] extends LawfulApplicative m : Prop where
  bind_pure_comp : ∀ (f : α → β) (x : m α), x >>= (pure ∘ f) = f <$> x
  bind_map       : ∀ (f : m (α → β)) (x : m α), f >>= (. <$> x) = f <*> x
  pure_bind      : ∀ (x : α) (f : α → m β), pure x >>= f = f x
  bind_assoc     : ∀ (x : m α) (f : α → m β) (g : β → m γ),
                     x >>= f >>= g = x >>= fun y => f y >>= g
```

### Ejemplo 2.1: La Mónada de Estado `MiEstado σ α` y la Demostración de sus Leyes
```lean
def MiEstado (σ : Type) (α : Type) : Type :=
  σ → α × σ

instance (σ : Type) : Monad (MiEstado σ) where
  pure a   := fun s => (a, s)
  bind m f := fun s =>
    let (a, s') := m s
    f a s'

-- En `MiEstado σ`, ¡las 3 leyes monádicas se cumplen definicionalmente (`rfl`)!
theorem miEstado_pure_bind {σ α β : Type} (a : α) (f : α → MiEstado σ β) :
    (pure a >>= f) = f a := rfl

theorem miEstado_bind_pure {σ α : Type} (m : MiEstado σ α) :
    (m >>= pure) = m := rfl

theorem miEstado_bind_assoc {σ α β γ : Type}
    (m : MiEstado σ α) (f : α → MiEstado σ β) (g : β → MiEstado σ γ) :
    ((m >>= f) >>= g) = (m >>= fun a => f a >>= g) := rfl
```

---

## 3. Cómo Desazucara Lean 4 la Notación `do` (`let mut`, `for`, `return`)

1. **Secuenciación básica:**
   ```lean
   do
     let x ← m1
     m2 x
   -- Se traduce a:
   Bind.bind m1 (fun x => m2 x)
   ```
2. **Variables mutables locales (`let mut x := v`):**
   El elaborador de `do` compila las variables `let mut` introduciendo automáticamente un transformador de estado local (`StateT`) o pasando el acumulador como argumento a través del bucle `ForIn.forIn`.
3. **Retorno temprano (`if c then return a`):**
   Se traduce usando un transformador de excepciones/cortocircuito interno (`ExceptT`).

```lean
-- Ejemplo de función pura escrita con `Id.run do` y verificada formalmente:
def buscarIndice {α : Type} (p : α → Bool) (xs : List α) : Option Nat := Id.run do
  let mut idx := 0
  for x in xs do
    if p x then
      return some idx
    idx := idx + 1
  return none

#eval buscarIndice (· > 10) [3, 7, 15, 2] -- some 2
```

---

## 4. Transformadores de Mónadas (`ReaderT`, `StateT`, `ExceptT`) y `MonadLift`

Cuando apilas varias mónadas, por ejemplo:
$$\texttt{AppM} := \texttt{ReaderT Config } (\texttt{ExceptT Error } (\texttt{StateM Store}))$$
Lean 4 sintetiza automáticamente instancias de `MonadLift`, `MonadReader Config AppM`, `MonadError Error AppM` y `MonadState Store AppM`. Gracias a ello, puedes llamar a `read`, `get`, `set` y `throw` directamente en el mismo bloque `do` sin escribir `lift` manualmente.
