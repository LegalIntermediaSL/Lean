# Cuaderno 04: Trazas Reales del Bucle `IA ↔ Compilador` — Cómo se Auto-Repara una IA en Lean 4

> **Jupyter Notebook (`.ipynb`) correspondiente:** [`notebooks/04_bucle_ia_compilador_autoreparacion.ipynb`](../../notebooks/04_bucle_ia_compilador_autoreparacion.ipynb)
> **Navegación:** [⬅ Cuaderno 03: Generalización de Invariantes](03_cuaderno_cuando_la_induccion_falla_generalizacion.md) | [Siguiente: Cuaderno 05 (Prompts y Auditoría) ➡](05_cuaderno_plantillas_prompts_agents_y_auditoria.md)

---

## 🎯 Objetivo del Cuaderno

Nadie —ni un matemático experto ni una IA de frontera— escribe a la primera 400 teoremas sin que el compilador rechace pasos intermedios. La diferencia entre una IA que se bloquea en bucle y una IA que resuelve teoremas complejos reside en **cómo interpreta los diagnósticos del compilador `lean`**.

En este cuaderno examinamos **tres casos reales de fallo $\to$ diagnóstico del kernel $\to$ reparación quirúrgica** ocurridos al desarrollar este repositorio (`M73`, `M76` y `M81`).

---

## Caso Real 1 — Cuando `omega` Falla en Expresiones No Lineales (`a * b` vs `b * a`)

### 🔴 Intento 1 Fallido de la IA
Al probar que la 2-forma simpléctica $\omega(u, u) = u_q u_p - u_p u_q$ vale $0$ en [`M73`](../../LeanTT/M73_HamiltonianMechanicsAndPoissonBrackets.lean), un primer intento ingenuo invoca `omega` directamente:

```text
theorem symplecticForm_self_FALLIDO (q p : Int) : q * p - p * q = 0 := by
  omega
```

**Diagnóstico exacto devuelto por `lean v4.35.0`:**
```text
error: omega could not prove the goal:
a possible counterexample may satisfy the constraints
  a - b ≤ -1
where
  a := q * p
  b := p * q
```

### 🧠 Cómo se Instruye a la IA para Leer este Error
* `omega` es un procedimiento de decisión para **aritmética lineal de Presburger** ($\mathbb{Z}$ con $+, -, \le$ y multiplicación por constantes).
* Como `q * p` y `p * q` son productos de dos variables, `omega` los abstrae como **dos átomos independientes `a` y `b`**!
* **Regla de reparación:** alinear primero el orden de las variables en cada monomio con `Int.mul_comm` antes de llamar a `omega`.

### 🟢 Intento 2 Reparado y Verificado

```lean
theorem symplecticForm_self_OK (q p : Int) : q * p - p * q = 0 := by
  -- 1. Unificamos ambos productos no lineales al mismo átomo `p * q`:
  rw [Int.mul_comm q p]
  -- 2. Ahora la meta es `p * q - p * q = 0` (`b - b = 0`), que `omega` cierra en 0 ms:
  omega
```

---

## Caso Real 2 — Asociatividad por la Izquierda y `Tactic rewrite failed`

### 🔴 Intento 1 Fallido de la IA
En `M81`, la IA quería probar `4 * ((k + 1) * (k + 1) * (k + 1)) = (4 * (k + 1)) * s` donde `let s := (k + 1) * (k + 1)`, y desplegó `dsimp [s]` antes de usar `← Nat.mul_assoc`:

```text
error: Tactic `rewrite` failed: Did not find an occurrence of the pattern
  4 * ((k + 1) * (k + 1)) * (k + 1)
in the target expression
  4 * ((k + 1) * (k + 1) * (k + 1)) = 4 * (k + 1) * ((k + 1) * (k + 1))
```

### 🧠 Diagnóstico Guiado por el Compilador
1. Al leer `target expression`, vemos que `(k + 1) * (k + 1) * (k + 1)` en Lean 4 agrupa **a la izquierda** como `((k + 1) * (k + 1)) * (k + 1) ≡ s * (k + 1)`.
2. Desplegar `s` duplicó innecesariamente el tamaño del término; manteniéndolo plegado como `s`, ¡solo hay que conmutar `s * (k + 1)` y asociar el `4`!

### 🟢 Intento 2 Reparado y Verificado (2 líneas limpias)

```lean
theorem factor_cubo_reparado (k : Nat) :
    let s := (k + 1) * (k + 1)
    4 * (s * (k + 1)) = (4 * (k + 1)) * s := by
  intro s
  rw [Nat.mul_comm s (k + 1), ← Nat.mul_assoc 4 (k + 1) s]
```

---

## Caso Real 3 — Explosión Combinatoria en Anillos Compuestos (`Cplx` en Mecánica Cuántica)

Al demostrar en [`M76`](../../LeanTT/M76_QuantumHilbertSpacesAndBraKet.lean) que $\langle A^\dagger \psi \mid \phi \rangle = \langle \psi \mid A \phi \rangle$ para matrices complejas $2 \times 2$:
* **Intento 1 (Fuerza bruta sobre `Int`):** abrir los 8 números complejos en 16 enteros `(re, im)` generó 32 monomios cúbicos con variables en distinto orden (`re3 * (re7 * re1)` vs `re7 * (re3 * re1)`), haciendo fallar a `omega`.
* **Intento 2 (Abstracción algebraica instruida por Blueprint):** demostrar una sola vez las leyes de anillo de `Cplx` (`conj_add`, `conj_mul`, `mul_comm`, `mul_assoc`, `add_mul`, `mul_add`) y operar **al nivel de `Cplx`** sin abrir jamás sus partes reales e imaginarias!

Comprobémoslo en vivo:

```lean
namespace Cuaderno04

structure Cplx where
  re : Int
  im : Int
  deriving Repr, DecidableEq

def Cplx.conj (z : Cplx) : Cplx := ⟨z.re, -z.im⟩
def Cplx.add (z w : Cplx) : Cplx := ⟨z.re + w.re, z.im + w.im⟩
def Cplx.mul (z w : Cplx) : Cplx := ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re⟩

-- Observa por qué `mul_assoc` sobre `Cplx` sale en UNA línea:
-- en `(u * v) * w = u * (v * w)`, las variables de `u`, `v` y `w` YA aparecen en el mismo orden!
theorem cplx_mul_assoc (u v w : Cplx) :
    Cplx.mul (Cplx.mul u v) w = Cplx.mul u (Cplx.mul v w) := by
  cases u; cases v; cases w
  dsimp [Cplx.mul]
  simp only [Cplx.mk.injEq, Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.mul_assoc]
  exact ⟨by omega, by omega⟩

end Cuaderno04
```

---

## Tabla de Consulta Rápida: Diagnóstico de Errores para Humanos e IA

| Mensaje del Compilador `lean` | Qué Significa Exactamente | Reparación Quirúrgica |
| :--- | :--- | :--- |
| `Tactic 'rewrite' failed: Did not find...` | Asociatividad implícita distinta o definición sin desplegar | Inspecciona la línea `in the target expression` y pasa argumentos explícitos a `Nat.mul_assoc a b c` o ejecuta `dsimp [def]`. |
| `omega could not prove... where a := x * y, b := y * x` | Dos monomios no lineales equivalentes pero con distinto orden sintáctico | Ejecuta `rw [Int.mul_comm x y]` antes de `omega`. |
| `failed to synthesize Decidable (MiPred x)` | `decide` no despliega un `def` semirreducible automáticamente | Cambia `def MiPred` a `abbrev MiPred`, o despliega con `dsimp [MiPred]` antes de decidir. |
| `simp made no progress` / `unused simp argument` | Un lema de `simp only [...]` ya no aparece tras un `dsimp` previo | Elimina el argumento sobrante sugerido literalmente por el `Hint:` del compilador. |
| `Application type mismatch` tras `congr 1` en estructuras | `congr 1` solo pela un argumento de un constructor multicampo | Sustituye `congr 1` por `simp only [MiEstructura.mk.injEq]` y resuelve la conjunción campo a campo. |

---

👉 **Siguiente cuaderno:** [**Cuaderno 05 — Plantillas de Prompts, `AGENTS.md` y Auditoría Anti-Trampas (`#print axioms` y No-Vacuidad)**](05_cuaderno_plantillas_prompts_agents_y_auditoria.md)
