# Módulo 11: Semántica Operacional — Paso Pequeño (*Small-Step*), Paso Grande (*Big-Step*), Confluencia y Progreso

> **Archivo Lean ejecutable asociado:** [`LeanTT/M11_OperationalSemantics.lean`](../LeanTT/M11_OperationalSemantics.lean)

---

## Índice del Módulo
1. [Inducción sobre Predicados Inductivos (Inducción sobre Derivaciones)](#1-inducción-sobre-predicados-inductivos-inducción-sobre-derivaciones)
2. [Semántica Natural o de Paso Grande (*Big-Step* `e ⇓ v`)](#2-semántica-natural-o-de-paso-grande-big-step-e--v)
3. [Semántica Estructural o de Paso Pequeño (*Small-Step* `e ⟶ e'`)](#3-semántica-estructural-o-de-paso-pequeño-small-step-e--e)
4. [Seguridad de Tipos Mediante Progreso y Preservación (Wright & Felleisen)](#4-seguridad-de-tipos-mediante-progreso-y-preservación-wright--felleisen)
5. [Demostración Completa de la Equivalencia `e ⇓ n ↔ e ⟶* .val n`](#5-demostración-completa-de-la-equivalencia-e--n--e--val-n)

---

## 1. Inducción sobre Predicados Inductivos (Inducción sobre Derivaciones)

En Lean 4, cuando defines una relación operacional como una familia inductiva en `Prop`:
```lean
namespace DemoSemantica

inductive Expr : Type where
  | val : Nat → Expr
  | add : Expr → Expr → Expr

inductive BigStep : Expr → Nat → Prop where
  | val : BigStep (.val n) n
  | add : BigStep e1 n1 → BigStep e2 n2 → BigStep (.add e1 e2) (n1 + n2)

infix:50 " ⇓ " => BigStep

end DemoSemantica
```
puedes hacer **inducción directamente sobre la prueba $h : e \Downarrow n$** (lo que en papel se llama *inducción sobre el árbol de derivación*), no solo sobre la sintaxis de $e$.

> **Consejo crucial con `induction h generalizing ...`:** Cuando haces inducción sobre una derivación $h : e \Downarrow n_1$ y en tu contexto tienes otra variable $n_2$ ligada a una segunda hipótesis $h_2 : e \Downarrow n_2$, usa siempre `induction h generalizing n2` para que la hipótesis inductiva sea universalmente cuantificada ($\forall n_2,\, \dots$).

---

## 2. Seguridad de Tipos Mediante Progreso y Preservación (Wright & Felleisen)

En la aproximación sintáctica a la seguridad de tipos (*Type Soundness*), un lenguaje tipado es seguro si cumple dos teoremas:

1. **Progreso (*Progress*):** Si $\vdash e : \tau$ es un término cerrado bien tipado, entonces o bien $e$ ya es un **valor**, o bien existe un término $e'$ tal que $e \longrightarrow e'$.
   ```lean
   namespace DemoSemantica

   inductive Step : Expr → Expr → Prop where
     | addVals  : Step (.add (.val n1) (.val n2)) (.val (n1 + n2))
     | addLeft  : Step e1 e1' → Step (.add e1 e2) (.add e1' e2)
     | addRight : Step e2 e2' → Step (.add (.val n1) e2) (.add (.val n1) e2')

   infix:50 " ⟶ " => Step

   -- Demostración del Teorema de Progreso para nuestro lenguaje `Expr`:
   theorem progress (e : Expr) :
       (∃ n : Nat, e = .val n) ∨ (∃ e' : Expr, e ⟶ e') := by
     induction e with
     | val n =>
       exact Or.inl ⟨n, rfl⟩
     | add e1 e2 ih1 ih2 =>
       right
       rcases ih1 with ⟨n1, rfl⟩ | ⟨e1', hs1⟩
       · rcases ih2 with ⟨n2, rfl⟩ | ⟨e2', hs2⟩
         · exact ⟨.val (n1 + n2), .addVals⟩
         · exact ⟨.add (.val n1) e2', .addRight hs2⟩
       · exact ⟨.add e1' e2, .addLeft hs1⟩

   end DemoSemantica
   ```
2. **Preservación (*Preservation* / *Subject Reduction*):** Si $\Gamma \vdash e : \tau$ y $e \longrightarrow e'$, entonces $\Gamma \vdash e' : \tau$.

---

## 3. Demostración de la Dirección Inversa: `e ⟶* .val n → e ⇓ n`

En [`LeanTT/M11_OperationalSemantics.lean`](../LeanTT/M11_OperationalSemantics.lean) demostramos que `e ⇓ n → e ⟶* .val n`. Para demostrar la dirección recíproca (`e ⟶* .val n → e ⇓ n`), el lema clave es la **expansión hacia atrás de un paso (*Head Expansion*)**:

$$\text{Si } e \longrightarrow e' \text{ y } e' \Downarrow n, \text{ entonces } e \Downarrow n.$$

```lean
open DemoSemantica

theorem step_bigStep {e e' : Expr} {n : Nat}
    (hs : e ⟶ e') (hb : e' ⇓ n) : e ⇓ n := by
  induction hs generalizing n with
  | addVals =>
    cases hb
    exact .add .val .val
  | addLeft hs1 ih =>
    cases hb with
    | add hb1 hb2 => exact .add (ih hb1) hb2
  | addRight hs2 ih =>
    cases hb with
    | add hb1 hb2 => exact .add hb1 (ih hb2)
```
