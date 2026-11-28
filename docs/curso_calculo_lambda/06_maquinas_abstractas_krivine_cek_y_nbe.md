# Lección 06: Máquinas Abstractas para el Cálculo $\lambda$ (Krivine KAM, Máquina CEK) y Normalización por Evaluación (NbE) en Lean 4

> **Navegación del Mini-Curso:** [⬅️ Lección 05: STLC, Normalización Fuerte y Sistema F](05_calculo_lambda_tipado_stlc_y_sistema_f.md) | [🏠 Índice del Mini-Curso $\lambda$](00_indice_minicurso_lambda.md)
>
> **Módulos ejecutables relacionados:** [`LeanTT/M27_NormalizationByEvaluation.lean`](../../LeanTT/M27_NormalizationByEvaluation.lean), [`LeanTT/M40_MiniDependentTypeChecker.lean`](../../LeanTT/M40_MiniDependentTypeChecker.lean) y [`LeanTT/M51_ContinuationPassingStyleCPS.lean`](../../LeanTT/M51_ContinuationPassingStyleCPS.lean).

---

## 1. ¿Por Qué los Intérpretes Reales No Hacen Sustitución Textual $t[u/x]$?

En la teoría matemática del cálculo $\lambda$, cada paso de $\beta$-reducción $(\lambda x.\, t)\; u \longrightarrow_\beta t[u/x]$ recorre todo el árbol sintáctico de $t$ para copiar $u$ en cada aparición de $x$. En la práctica, hacer copias de árboles sintácticos en cada llamada a función sería catastróficamente lento ($O(|t| \cdot |u|)$ por paso).

En **1964**, **Peter Landin** (al diseñar la máquina **SECD**) introdujo la idea clave de todos los intérpretes y máquinas virtuales funcionales modernos: las **Clausuras (*Closures*)** y los **Entornos (*Environments*)**:
* En lugar de sustituir físicamente $x$ por $u$ dentro del código de $t$, **retrasamos la sustitución** guardando el valor de $x$ en una lista o array llamado el **entorno** $E = [v_0, v_1, \dots]$.
* Una función evaluada en un entorno $E$ se empaqueta como una **clausura** $\langle \lambda.\, t,\; E \rangle$ que recuerda el código $\lambda.\, t$ junto con el entorno léxico $E$ donde fue creada.

---

## 2. Comparativa de las 4 Grandes Arquitecturas de Ejecución del Cálculo $\lambda$

| Máquina / Algoritmo | Autores y Año | Estrategia | Estado de la Máquina | ¿Dónde se Usa? |
| :--- | :--- | :--- | :--- | :--- |
| **1. Máquina SECD** | Peter Landin (1964) | *Call-by-Value* (CBV) | `(S, E, C, D)`: Stack, Environment, Control, Dump | Lispkit, máquinas virtuales funcionales clásicas |
| **2. Máquina de Krivine (KAM)** | Jean-Louis Krivine (1985/2007) | *Call-by-Name* (CBN / Cabeza débil) | `(t, E, S)`: Término actual $t$, Entorno de clausuras $E$, Pila de argumentos $S$ | Reducción `whnf` en kernels de asistentes de pruebas (Coq/Lean) |
| **3. Máquina CEK** | Felleisen & Friedman (1986) | *Call-by-Value* (CBV) | `(C, E, K)`: Control $C$, Entorno $E$, Continuación estructurada $K$ | Semántica operacional de Scheme, ML y WebAssembly |
| **4. Normalización por Evaluación (NbE)** | Berger & Schwichtenberg (1991), Coquand (1996) | Forma normal completa $\beta\eta$ (bajo $\lambda$) | `eval` (Sintaxis $\to$ Dominio Semántico con `Ne`/`Val`) + `reify` (Semántica $\to$ `Nf`) | Chequeo de conversión en Agda, Idris 2 y formalización en [`LeanTT/M27`](../../LeanTT/M27_NormalizationByEvaluation.lean) |

---

## 3. La Máquina Abstracta de Krivine (KAM) Paso a Paso

La **Máquina de Krivine** es la forma más elegante jamás descubierta de ejecutar el cálculo $\lambda$ con índices de De Bruijn en estrategia *Call-by-Name*. Su estado es una simple tripleta $\langle t,\; e,\; \pi \rangle$:
* **$t$:** el término con índices de De Bruijn que estamos inspeccionando.
* **$e$:** el entorno actual (una lista de clausuras $c_0 :: c_1 :: \dots$, una por cada índice de De Bruijn `#0, #1, ...`).
* **$\pi$:** la pila (*stack*) de argumentos pendientes de ser consumidos (cada argumento en la pila es también una clausura $\langle u, e' \rangle$).

Sus **tres únicas reglas de transición** son:

1. **Aplicación (*Push*):** Al encontrar $t_1\; t_2$, empaquetamos el argumento $t_2$ con el entorno actual $e$ en la pila $\pi$ y pasamos a evaluar la función $t_1$:
   $$\langle t_1\; t_2,\;\; e,\;\; \pi \rangle \;\longrightarrow_{\text{KAM}}\; \langle t_1,\;\; e,\;\; \langle t_2, e \rangle :: \pi \rangle$$
2. **Abstracción $\lambda$ (*Pop / Grab*):** Al encontrar $\lambda.\, b$ con un argumento $c$ esperando en la cima de la pila $\pi$, desapilamos $c$, lo colocamos en la posición `#0` del entorno $e$ y entramos en el cuerpo $b$:
   $$\langle \lambda.\, b,\;\; e,\;\; c :: \pi \rangle \;\longrightarrow_{\text{KAM}}\; \langle b,\;\; c :: e,\;\; \pi \rangle$$
3. **Variable de De Bruijn (*Lookup*):** Al encontrar el índice `#i`, extraemos la $i$-ésima clausura $\langle t', e' \rangle$ del entorno $e$ e instalamos $t'$ y su entorno léxico $e'$ como estado actual:
   $$\langle \text{var } i,\;\; e,\;\; \pi \rangle \;\longrightarrow_{\text{KAM}}\; \langle t',\;\; e',\;\; \pi \rangle \qquad (\text{donde } e[i] = \langle t', e' \rangle)$$

---

## 4. Implementación Ejecutable de la Máquina de Krivine (KAM) en Lean 4

Implementemos la Máquina Abstracta de Krivine completa en Lean 4 (extendida con constantes numéricas para observar el resultado final) y verifiquemos su ejecución por `rfl`:

```lean
namespace CursoLambda.Leccion06

/-- Términos del cálculo λ con índices de De Bruijn y literales naturales -/
inductive KAMTerm where
  | var : Nat → KAMTerm
  | lam : KAMTerm → KAMTerm
  | app : KAMTerm → KAMTerm → KAMTerm
  | lit : Nat → KAMTerm
  deriving Repr, DecidableEq

/-- Una Clausura de Krivine empaqueta un término `KAMTerm` con su entorno léxico `List Closure` -/
inductive Closure where
  | mk : KAMTerm → List Closure → Closure
  deriving Repr

/-- Búsqueda por índice de De Bruijn en el entorno de clausuras -/
@[simp]
def lookupEnv : List Closure → Nat → Option Closure
  | [],      _     => none
  | c :: _,  0     => some c
  | _ :: es, i + 1 => lookupEnv es i

/-- Ejecutor de la Máquina Abstracta de Krivine (KAM) acotado por `fuel` pasos:
    Estado: `(términoActual, entornoActual, pilaDeArgumentos)` -/
@[simp]
def runKAM : Nat → KAMTerm → List Closure → List Closure → Option Nat
  | 0, _, _, _ => none
  | _ + 1, .lit n, _, [] =>
    -- Éxito: llegamos a un literal numérico con la pila de argumentos vacía
    some n
  | fuel + 1, .app f a, env, stack =>
    -- Regla 1 (Push): apilamos la clausura `(a, env)` y evaluamos `f`
    runKAM fuel f env (.mk a env :: stack)
  | fuel + 1, .lam body, env, arg :: stack =>
    -- Regla 2 (Grab): desapilamos `arg` y lo ligamos al índice `#0` del entorno
    runKAM fuel body (arg :: env) stack
  | fuel + 1, .var i, env, stack =>
    -- Regla 3 (Lookup): abrimos la clausura número `i` del entorno
    match lookupEnv env i with
    | some (.mk t' env') => runKAM fuel t' env' stack
    | none               => none
  | _ + 1, _, _, _ => none

/-- Ejemplo: Evaluar en la Máquina de Krivine `((λx. λy. x) 42) 999`
    (`combK 42 999`), verificando que descarta `999` sin evaluarlo y devuelve `42`! -/
def termK42_999 : KAMTerm :=
  .app (.app (.lam (.lam (.var 1))) (.lit 42)) (.lit 999)

theorem krivine_evalua_K_42_999 :
    runKAM 10 termK42_999 [] [] = some 42 :=
  rfl

end CursoLambda.Leccion06
```

---

## 5. De la Máquina de Krivine a la Normalización por Evaluación (NbE)

La Máquina de Krivine se detiene tan pronto como llega a una abstracción $\lambda.\, b$ con la pila de argumentos vacía ($\pi = []$). Ese estado se llama **Forma Normal Débil de Cabeza (*Weak Head Normal Form*, `whnf`)**.

Pero en un asistente de tipos dependientes como Lean 4, cuando comparamos dos funciones $\lambda x.\, t_1$ y $\lambda x.\, t_2$ dentro de un tipo, necesitamos reducir **también debajo del $\lambda$**.
Como demostramos formalmente en el **[Módulo 27 (`LeanTT/M27_NormalizationByEvaluation.lean`)](../../LeanTT/M27_NormalizationByEvaluation.lean)**, el algoritmo de **Normalización por Evaluación (NbE)** resuelve esto en dos fases:
1. Evalúa el término hacia un valor semántico (`Val`).
2. Cuando `reify` necesita inspeccionar el cuerpo de una función semántica, crea una **variable fresca neutra (`reflect (Ne.var lvl)`)**, se la pasa como argumento a la función y reifica recursivamente el resultado, obteniendo la forma normal $\beta\eta$ completa sin realizar sustituciones sintácticas.

---

## 6. Ejercicio Práctico de la Lección 06

### Ejercicio 6.1: Traza de la Máquina de Krivine con Aplicación de Orden Superior
Construye el `KAMTerm` correspondiente a `(λf. f 77) (λx. x)` y demuestra en Lean 4 mediante `rfl` que `runKAM 10 term [] [] = some 77`.

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
open CursoLambda.Leccion06

-- `(λf. f 77) (λx. x)` en De Bruijn es `(λ. #0 77) (λ. #0)`:
def termApplyId77 : KAMTerm :=
  .app (.lam (.app (.var 0) (.lit 77))) (.lam (.var 0))

theorem krivine_apply_id_77 :
    runKAM 10 termApplyId77 [] [] = some 77 :=
  rfl
```
</details>

---

⬅️ [**Volver al Índice del Mini-Curso de Cálculo Lambda (`00_indice_minicurso_lambda.md`)**](00_indice_minicurso_lambda.md)
