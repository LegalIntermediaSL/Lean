# Módulo 10: Metateoría del Cálculo Lambda Simplemente Tipado (STLC) en Lean 4

> **Archivo Lean ejecutable asociado:** [`LeanTT/M10_MetatheorySTLC.lean`](../LeanTT/M10_MetatheorySTLC.lean)

---

## 1. Sintaxis Intrínsecamente Tipada (*Intrinsically Typed Syntax*)

Cuando formalizamos un lenguaje de programación o un cálculo lambda dentro de un asistente de pruebas, existen dos enfoques:

1. **Enfoque Extrínseco (*Curry-style*):** Definir primero términos crudos `RawTerm` y luego una relación inductiva separada `HasType : Ctx → RawTerm → Ty → Prop`. Esto obliga a demostrar en cada paso que las transformaciones preservan el buen tipado y a lidiar con casos imposibles.
2. **Enfoque Intrínseco (*Church-style* / Familias Inductivas Dependientes):** Indexar directamente el tipo de los términos por el **contexto de tipado $\Gamma$** y el **tipo $\tau$**:
   $$\texttt{Term} : \texttt{Ctx} \to \texttt{Ty} \to \texttt{Type}$$

De este modo, un habitante de `Term Γ τ` es **por construcción** una derivación válida de $\Gamma \vdash t : \tau$. Los términos mal tipados o con variables libres fuera de ámbito ni siquiera pueden representarse.

---

## 2. Índices de De Bruijn Tipados (`Lookup Γ τ`)

En lugar de nombres de variables con cadenas (`"x"`, `"y"`), representamos una variable mediante su posición en el contexto $\Gamma = [\tau_0, \tau_1, \dots, \tau_{n-1}]$:

```lean
inductive Var : Ctx → Ty → Type where
  | zero : {Γ : Ctx} → {τ : Ty} → Var (τ :: Γ) τ
  | succ : {Γ : Ctx} → {σ τ : Ty} → Var Γ τ → Var (σ :: Γ) τ
```

* `Var.zero` apunta a la variable ligada por el $\lambda$ más interno.
* `Var.succ v` salta un $\lambda$ hacia afuera.

Por ejemplo, el combinador $K = \lambda x : \sigma.\, \lambda y : \tau.\, x$ se escribe sin ningún nombre de variable como:
$$\lambda.\, \lambda.\, \texttt{var}(\texttt{succ }\texttt{zero})$$

---

## 3. Renombramiento (Debilitamiento) y Sustitución Paralela

Para definir la $\beta$-reducción $(\lambda x.\, t)\; u \to t[x := u]$ en sintaxis intrínsecamente tipada y demostrar que preserva los tipos por construcción, seguimos la estructura algebraica de **Altenkirch-Reus / Benton-Hur-Kennedy-McBride**:

1. **Renombramiento (`Ren Γ Δ`):** Una transformación de contextos que envía toda variable `Var Γ τ` a una variable `Var Δ τ`:
   $$\text{Ren }\Gamma\;\Delta := \forall \tau,\, \text{Var }\Gamma\;\tau \to \text{Var }\Delta\;\tau$$
   Al atravesar un $\lambda x : \sigma$, el renombramiento se **levanta** (*lift*) a `Ren (σ :: Γ) (σ :: Δ)`.
2. **Sustitución Paralela (`Sub Γ Δ`):** Una transformación que envía toda variable `Var Γ τ` a un **término bien tipado** `Term Δ τ`:
   $$\text{Sub }\Gamma\;\Delta := \forall \tau,\, \text{Var }\Gamma\;\tau \to \text{Term }\Delta\;\tau$$
   Al atravesar un $\lambda x : \sigma$, la sustitución se levanta debilitando todos los términos con `Var.succ`.

Con esto, la **preservación de tipos (*Subject Reduction*)** para la sustitución queda garantizada estáticamente por el propio sistema de tipos de Lean 4.

---

## 4. Semántica Denotacional y Evaluador Total

Aprovechando que los tipos del STLC se interpretan directamente en tipos de Lean 4:
$$\llbracket \texttt{base} \rrbracket = \texttt{Nat}, \qquad \llbracket \sigma \Rightarrow \tau \rrbracket = \llbracket \sigma \rrbracket \to \llbracket \tau \rrbracket$$
podemos escribir un evaluador denotacional `eval : Term Γ τ → Env Γ → τ.denote` sin un solo `Option`, sin errores de tipo en tiempo de ejecución y cuya terminación prueba inmediatamente que el STLC es fuertemente normalizante.
