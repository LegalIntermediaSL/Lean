# Módulo 10: Metateoría del Cálculo Lambda Simplemente Tipado (STLC) con Tipos Dependientes

> **Archivo Lean ejecutable asociado:** [`LeanTT/M10_MetatheorySTLC.lean`](../LeanTT/M10_MetatheorySTLC.lean)

---

## Índice del Módulo
1. [Por Qué la Sintaxis Intrínsecamente Tipada Revoluciona la Metateoría](#1-por-qué-la-sintaxis-intrínsecamente-tipada-revoluciona-la-metateoría)
2. [Representación de Contextos $\Gamma$ y Variables de De Bruijn Tipadas (`Var Γ τ`)](#2-representación-de-contextos-gamma-y-variables-de-de-bruijn-tipadas-var-γ-τ)
3. [El AST Intrínseco `Term Γ τ` como Codificación de las Reglas de Tipado](#3-el-ast-intrínseco-term-γ-τ-como-codificación-de-las-reglas-de-tipado)
4. [Álgebra de Renombramientos (`Ren`) y Sustituciones Paralelas (`Sub`)](#4-álgebra-de-renombramientos-ren-y-sustituciones-paralelas-sub)
5. [Semántica Denotacional, Entornos Tipados (`Env Γ`) y Evaluación Total](#5-semántica-denotacional-entornos-tipados-env-γ-y-evaluación-total)
6. [Normalización por Evaluación (NbE) y Lema de Corrección Semántica](#6-normalización-por-evaluación-nbe-y-lema-de-corrección-semántica)

---

## 1. Por Qué la Sintaxis Intrínsecamente Tipada Revoluciona la Metateoría

En los libros de texto tradicionales sobre lenguajes de programación (como *Types and Programming Languages* de Pierce), se define primero una gramática libre de contexto de términos sin tipar:
$$t ::= x \mid \lambda x : \tau.\, t \mid t_1\; t_2$$
y aparte una relación ternaria $\Gamma \vdash t : \tau$. Este enfoque **extrínseco** obliga a probar decenas de lemas administrativos (inversión del tipado, unicidad de tipos, debilitamiento de derivaciones, preservación de tipos bajo sustitución) antes de poder siquiera escribir un evaluador.

Con los **tipos dependientes de Lean 4**, podemos fusionar la sintaxis y el sistema de tipos en una única familia inductiva indexada:
$$\texttt{Term} : \texttt{Ctx} \to \texttt{Ty} \to \texttt{Type}$$

---

## 2. Representación de Contextos $\Gamma$ y Variables de De Bruijn Tipadas (`Var Γ τ`)

Un contexto $\Gamma$ es una lista de tipos `List Ty`, donde la cabeza de la lista representa la variable ligada más recientemente:

```lean
namespace DemoSTLC

inductive Ty : Type where
  | nat  : Ty
  | bool : Ty
  | arr  : Ty → Ty → Ty

infixr:70 " ⇒ " => Ty.arr
abbrev Ctx := List Ty

inductive Var : Ctx → Ty → Type where
  | zero : {Γ : Ctx} → {τ : Ty} → Var (τ :: Γ) τ
  | succ : {Γ : Ctx} → {σ τ : Ty} → Var Γ τ → Var (σ :: Γ) τ

end DemoSTLC
```

### Ejemplo 2.1: Cómo Representan los Constructores de `Var` la Regla de Variable
La regla de inferencia lógica para las variables:
$$\frac{(x : \tau) \in \Gamma}{\Gamma \vdash x : \tau}$$
está codificada constructivamente por `Var Γ τ`:
* En el contexto $\Gamma = [\texttt{nat}, \texttt{bool}, \texttt{nat} \Rightarrow \texttt{bool}]$:
  * `Var.zero` tiene tipo `Var Γ .nat`.
  * `Var.succ Var.zero` tiene tipo `Var Γ .bool`.
  * `Var.succ (Var.succ Var.zero)` tiene tipo `Var Γ (.nat ⇒ .bool)`.
  * Intentar construir `Var.succ (Var.succ (Var.succ Var.zero))` es un **error de tipos en tiempo de compilación** porque el resto del contexto es `[]`.

---

## 3. El AST Intrínseco `Term Γ τ` como Codificación de las Reglas de Tipado

Cada constructor de `Term` es literalmente una regla de inferencia de Gentzen del STLC:

$$
\frac{v \in \text{Var }\Gamma\;\tau}{\Gamma \vdash \text{var }v : \tau}
\qquad
\frac{\sigma :: \Gamma \vdash b : \tau}{\Gamma \vdash \text{lam }b : \sigma \Rightarrow \tau}
\qquad
\frac{\Gamma \vdash f : \sigma \Rightarrow \tau \qquad \Gamma \vdash a : \sigma}{\Gamma \vdash \text{app }f\;a : \tau}
$$

```lean
namespace DemoSTLC

inductive Term : Ctx → Ty → Type where
  | var : {Γ : Ctx} → {τ : Ty} → Var Γ τ → Term Γ τ
  | lam : {Γ : Ctx} → {σ τ : Ty} → Term (σ :: Γ) τ → Term Γ (σ ⇒ τ)
  | app : {Γ : Ctx} → {σ τ : Ty} → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ

end DemoSTLC
```

---

## 4. Álgebra de Renombramientos (`Ren`) y Sustituciones Paralelas (`Sub`)

¿Por qué definimos primero el **renombramiento** `Ren Γ Δ` y luego la **sustitución** `Sub Γ Δ`?
Porque cuando una sustitución $s : \text{Sub }\Gamma\;\Delta$ atraviesa un ligador $\lambda (x : \sigma)$, necesitamos extender $s$ a una sustitución $\text{lift}(s) : \text{Sub }(\sigma :: \Gamma)\;(\sigma :: \Delta)$:
* La variable recién ligada `Var.zero` se envía a sí misma: `Term.var Var.zero`.
* Cada variable anterior `Var.succ x` se envía al término `s x : Term Δ τ`, ¡pero debilitado al nuevo contexto `σ :: Δ`! Ese debilitamiento (`weaken : Term Δ τ → Term (σ :: Δ) τ`) es simplemente un renombramiento con `Var.succ`.

---

## 5. Semántica Denotacional, Entornos Tipados (`Env Γ`) y Evaluación Total

La función `Ty.denote : Ty → Type` es un ejemplo paradigmático de **tipo dependiente grande** (una función que devuelve un `Type`):
* `Ty.nat.denote = Nat`
* `Ty.bool.denote = Bool`
* `(σ ⇒ τ).denote = σ.denote → τ.denote`

Gracias a ello, la evaluación `eval : Term Γ τ → Env Γ → τ.denote` mapea directamente:
* `Term.lam body` a una verdadera función de Lean `fun v => eval body (.cons v env)`.
* `Term.app f a` a la verdadera aplicación de Lean `(eval f env) (eval a env)`.

---

## 6. Lema de Composición de Renombramiento y Sustitución Semántica

Demostremos en Lean 4 que evaluar un término renombrado `t.rename ρ` en un entorno `env : Env Δ` es idéntico a evaluar `t` en el entorno reindexado:

```lean
namespace DemoSTLC

def Ty.denote : Ty → Type
  | .nat  => Nat
  | .bool => Bool
  | σ ⇒ τ => σ.denote → τ.denote

inductive Env : Ctx → Type where
  | nil  : Env []
  | cons : {Γ : Ctx} → {τ : Ty} → τ.denote → Env Γ → Env (τ :: Γ)

def Env.lookup : {Γ : Ctx} → {τ : Ty} → Env Γ → Var Γ τ → τ.denote
  | _ :: _, _, .cons v _,   .zero   => v
  | _ :: _, _, .cons _ env, .succ x => env.lookup x

-- Reindexación de un entorno `Env Δ` a lo largo de un renombramiento `ρ : Ren Γ Δ`:
def Env.reindex {Γ Δ : Ctx} (ρ : ∀ {τ}, Var Γ τ → Var Δ τ) (env : Env Δ) : Env Γ :=
  match Γ with
  | []      => .nil
  | _ :: _  => .cons (env.lookup (ρ .zero)) (env.reindex (fun x => ρ (.succ x)))

end DemoSTLC
```
