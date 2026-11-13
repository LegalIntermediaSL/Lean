# Módulo 17: Guía de Equivalencias — De Python/TypeScript, Haskell/OCaml y Coq/Agda a Lean 4

Esta guía traduce los conceptos que ya conoces de otros lenguajes hacia su equivalente idiomático en **Lean 4**.

---

## 1. De Python / TypeScript / Rust a Lean 4

| Concepto en Python / TS / Rust | Equivalente en Lean 4 | Ejemplo en Lean 4 |
| :--- | :--- | :--- |
| `def f(x: int, y: int) -> int:` | `def f (x y : Int) : Int :=` | `def f (x y : Int) : Int := x + y` |
| `lambda x: x + 1` / `(x) => x + 1` | `fun x => x + 1` o `(· + 1)` | `List.map (· + 1) [1, 2, 3]` |
| `struct User { id: u64, name: String }` | `structure User where` | `structure User where id : Nat; name : String` |
| `enumShape { Circle(f64), Rect(f64, f64) }` | `inductive Shape where` | `inductive Shape \| circle (r : Float) \| rect (w h : Float)` |
| `Option<T>` (`Some(x)` / `None`) | `Option α` (`some x` / `none`) | `match opt with \| some x => x \| none => 0` |
| `Result<T, E>` (`Ok(x)` / `Err(e)`) | `Except ε α` (`.ok x` / `.error e`) | `Except.ok 42` |
| Interpolación `f"Hola {nombre}"` | `s!"Hola {nombre}"` | `#eval s!"2 + 2 = {2 + 2}"` |
| Bucle imperativo con variable local | `Id.run do let mut acc := 0; for x in xs do ...` | Compila a código funcional puro sin mutación global |
| `assert(x > 0)` *(falla en ejecución)* | `(h : x > 0)` o `{ x : Nat // x > 0 }` | **Verificado en compilación (0 fallos en ejecución)** |

---

## 2. De Haskell / OCaml a Lean 4

| Haskell | Lean 4 | Diferencia Clave |
| :--- | :--- | :--- |
| Evaluación perezosa (*Lazy*) por defecto | Evaluación estricta (*Call-by-Value*) por defecto | En Lean 4 la pereza es explícita con `Thunk α` |
| Funciones parciales permitidas (`head [] = error`) | **Todas las funciones son totales** (o marcadas `partial def`) | Evita la inconsistencia lógica del tipo vacío |
| `data Vec a = ...` (GADTs con `DataKinds`) | `inductive Vec (α : Type) : Nat → Type` | Los tipos dependientes son nativos: no necesitas `TypeFamilies` ni `SingI` |
| `f :: forall a. [a] -> Int` | `def f {α : Type} (xs : List α) : Nat` | `{α : Type}` marca argumentos implícitos inferidos por unificación |
| `fmap` / `<$>` y `>>=` | `Functor.map` / `<$>` y `>>=` | En Lean 4 existe además `LawfulFunctor` y `LawfulMonad` con pruebas |
| `[x * 2 \| x <- xs]` | `xs.map (· * 2)` o bloques `do` | La notación `do` de Lean 4 soporta `let mut`, `for`, `break` y `return` temprano |

---

## 3. De Coq (Rocq) / Agda a Lean 4

| Coq / Rocq | Agda | Lean 4 |
| :--- | :--- | :--- |
| `Theorem T : P. Proof. ... Qed.` | `T : P; T = ...` | `theorem T : P := by ...` (o término directo `:= ...`) |
| `Inductive` / `Fixpoint` / `Definition` | `data` / función con patrones | `inductive` / `def` (detecta recursión automáticamente) |
| `forall x : A, B x` | `(x : A) → B x` | Ambos: `∀ x : A, B x` y `(x : A) → B x` son idénticos |
| `{ x : A \| P x }` (`sig`) | `Σ[ x ∈ A ] P x` | `{ x : A // P x }` (`Subtype`) y `(x : A) × B x` (`Sigma`) |
| `intros`, `destruct`, `inversion` | Reconocimiento de patrones | `intro`, `rcases`, `cases`, `nomatch` |
| `rewrite H` / `rewrite <- H` | `rewrite eq` | `rw [h]` / `rw [← h]` *(nota: `rw` de Lean intenta `rfl` al final automáticamente)* |
| `lia` / `omega` | Solver de aritmética | `omega` (integrado en el núcleo de Lean 4) |
| Universos acumulativos + `Set` | `Set ℓ` predicativos (con `--without-K` / `--cubical`) | `Prop` (`Sort 0`, impredicativo + UIP definicional) y `Type u` (`Sort (u+1)`) + `Quot` primitivo |
| Metaprogramación en `Ltac2` / `MetaCoq` | Reflexión en Agda | **Lean 4 es auto-alojado**: las tácticas se escriben directamente en Lean 4 (`MetaM` / `TacticM`) |
