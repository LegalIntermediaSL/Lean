# Lección 03: Codificaciones de Church y de Scott (Booleanos, Numerales, Listas) y Combinadores de Punto Fijo ($Y, \Theta, Z$)

> **Navegación del Mini-Curso:** [⬅️ Lección 02: Reducciones y Confluencia](02_reducciones_beta_eta_y_confluencia.md) | [🏠 Índice](00_indice_minicurso_lambda.md) | [➡️ Lección 04: Lógica Combinatoria SKI](04_logica_combinatoria_ski_y_abstraccion.md)
>
> **Módulos ejecutables relacionados:** [`LeanTT/M01_LambdaCalculus.lean`](../../LeanTT/M01_LambdaCalculus.lean) y [`LeanTT/M26_SystemFAndParametricity.lean`](../../LeanTT/M26_SystemFAndParametricity.lean).

---

## 1. ¿Cómo Programar Números, Booleanos y Listas Si Solo Existen Funciones?

En el cálculo $\lambda$ puro no existen números, ni booleanos, ni tuplas, ni punteros: **todo objeto es una función**.
La idea fundamental de Alonzo Church fue **identificar cada dato con su propio eliminador (su función de plegado o iterador `fold`)**:
* Un **booleano** no es un bit en memoria: es una **función que recibe dos opciones $(t, f)$ y elige una de ellas**.
* Un **par ordenado** $\langle a, b \rangle$ es una **función que espera un selector $s$ y le entrega $s\; a\; b$**.
* Un **número natural** $n$ es una **función de orden superior que recibe un paso $f$ y una base $x$, e itera $f$ exactamente $n$ veces sobre $x$**: $f^{(n)}(x)$.

---

## 2. Tabla de las Codificaciones de Church (en Cálculo $\lambda$ Puro y en Sistema F / Lean 4)

| Estructura / Operación | Término $\lambda$ de Church | Tipo Polimórfico en Sistema F (Lean 4) |
| :--- | :--- | :--- |
| **Tipo Booleano** `CBool` | — | `(α : Type) → α → α → α` |
| `cTrue` | $\lambda t.\, \lambda f.\, t$ | `fun _ t _ => t` |
| `cFalse` | $\lambda t.\, \lambda f.\, f$ | `fun _ _ f => f` |
| `cAnd` ($p \land q$) | $\lambda p.\, \lambda q.\, p\; q\; p$ | `fun p q α t f => p α (q α t f) f` |
| `cNot` ($\neg p$) | $\lambda p.\, \lambda t.\, \lambda f.\, p\; f\; t$ | `fun p α t f => p α f t` |
| **Tipo Numeral** `CNat` | — | `(α : Type) → (α → α) → α → α` |
| $c_0$ (`zero`) | $\lambda f.\, \lambda x.\, x$ | `fun _ _ x => x` |
| $c_1, c_2, c_3$ | $\lambda f.\, \lambda x.\, f(x),\;\; \lambda f.\, \lambda x.\, f(f(x)), \dots$ | Iterador $n$-ésimo |
| `cSucc` ($n + 1$) | $\lambda n.\, \lambda f.\, \lambda x.\, f\; (n\; f\; x)$ | Un paso adicional de $f$ sobre $n\; f\; x$ |
| `cAdd` ($m + n$) | $\lambda m.\, \lambda n.\, \lambda f.\, \lambda x.\, m\; f\; (n\; f\; x)$ | Aplicar $f$ $n$ veces y luego $m$ veces más |
| `cMul` ($m \cdot n$) | $\lambda m.\, \lambda n.\, \lambda f.\, m\; (n\; f)$ | Componer el iterador $n$-ésimo $m$ veces ($f \mapsto n\; f$) |

---

## 3. Codificación de Church vs. Codificación de Dana Scott (1962)

En la codificación de Church, un dato representa su **recursor completo (`foldr`)**. Por eso sumar y multiplicar numerales de Church toma tiempo $O(1)$ de construcción de clausura, pero **calcular el predecesor $n - 1$ de un numeral de Church** (descubierto por Stephen Kleene en 1935 mientras estaba en la consulta del dentista) requiere reconstruir pares desde $0$ hasta $n$ en tiempo **$O(n)$**!

En **1962**, **Dana Scott** descubrió una codificación alternativa: en lugar de identificar un dato con su recursor completo (`fold`), **la Codificación de Scott identifica un dato con su análisis de casos superficial (`match` de 1 nivel)**:
* En la codificación de Scott, el número $0$ es $\lambda z.\, \lambda s.\, z$, y el sucesor $\text{succ}(n)$ es $\lambda z.\, \lambda s.\, s\; n$ (¡le pasa $n$ directamente al manejador $s$ sin recursión!).
* **Ventaja de Scott:** ¡El predecesor $\text{pred}(n)$ toma tiempo constante **$O(1)$**: $\text{pred}(n) = n\; 0\; (\lambda k.\, k)$!

---

## 4. Recursión General sin Nombres: Los Combinadores de Punto Fijo ($Y$, $\Theta$ y $Z$)

En el cálculo $\lambda$ puro las funciones son anónimas: el cuerpo de una función no puede llamarse a sí mismo por su nombre. ¿Cómo se escribe entonces una función recursiva como el factorial?

Mediante un **Combinador de Punto Fijo** $F$: un término cerrado tal que para cualquier funcional $g$,
$$F\; g \;\equiv_\beta\; g\; (F\; g)$$

1. **El Combinador $Y$ de Haskell Curry (para evaluación perezosa / Call-by-Name):**
   $$Y \;\equiv\; \lambda g.\, (\lambda x.\, g\; (x\; x))\; (\lambda x.\, g\; (x\; x))$$
   Veamos su reducción en 1 paso:
   $$Y\; g \;\longrightarrow_\beta\; (\lambda x.\, g\; (x\; x))\; (\lambda x.\, g\; (x\; x)) \;\longrightarrow_\beta\; g\; \big((\lambda x.\, g\; (x\; x))\; (\lambda x.\, g\; (x\; x))\big) \;\equiv\; g\; (Y\; g)$$
2. **El Combinador $\Theta$ de Alan Turing (1937):**
   Mientras que $Y\; g$ solo es convertible con $g(Y\; g)$, Turing diseñó $\Theta \equiv A\; A$ donde $A \equiv \lambda x.\, \lambda y.\, y\; (x\; x\; y)$, que se **reduce directamente** en dos pasos a $g(\Theta\; g)$:
   $$\Theta\; g \;=\; A\; A\; g \;\longrightarrow_\beta\; (\lambda y.\, y\; (A\; A\; y))\; g \;\longrightarrow_\beta\; g\; (A\; A\; g) \;\equiv\; g\; (\Theta\; g)$$
3. **El Combinador $Z$ de Plotkin (para lenguajes estrictos / Call-by-Value):**
   Si evaluamos $Y\; g$ en un lenguaje estricto (CBV), el argumento $(x\; x)$ se evalúa infinitamente antes de entrar en $g$. Para frenar la evaluación aplicamos una **$\eta$-expansión protectora** $\lambda v.\, (x\; x)\; v$:
   $$Z \;\equiv\; \lambda g.\, (\lambda x.\, g\; (\lambda v.\, x\; x\; v))\; (\lambda x.\, g\; (\lambda v.\, x\; x\; v))$$

---

## 5. Laboratorio Ejecutable en Lean 4: Aritmética de Church y Predecesor de Kleene

Todo el bloque siguiente compila y se ejecuta en Lean 4:

```lean
namespace CursoLambda.Leccion03

/-- Tipo de los Numerales de Church en el Sistema F de Lean 4 -/
def CNat : Type 1 := (α : Type) → (α → α) → α → α

def cZero : CNat := fun _ _ x => x
def cSucc (n : CNat) : CNat := fun α f x => f (n α f x)
def cAdd  (m n : CNat) : CNat := fun α f x => m α f (n α f x)
def cMul  (m n : CNat) : CNat := fun α f x => m α (n α f)

/-- El Truco del Dentista de Kleene (1935) para el Predecesor de Church `cPred`:
    Iteramos sobre pares `(Nat × Nat)` comenzando en `(0, 0)` con el paso `(a, b) ↦ (b, b + 1)`
    y al final tomamos la primera coordenada! -/
def cPred (n : CNat) : CNat :=
  fun α f x =>
    (n ((α → α) → α)
       (fun g h => h (g f))
       (fun _ => x)
       (fun u => u))

/-- Conversión de `CNat` a `Nat` nativo de Lean 4 para inspeccionar resultados -/
def toNat (n : CNat) : Nat :=
  n Nat Nat.succ 0

def c2 : CNat := cSucc (cSucc cZero)
def c3 : CNat := cSucc c2

/-- TEOREMA: Verificación por cómputo (`rfl`) de la suma, producto y predecesor de Kleene en Church! -/
theorem church_aritmetica_y_kleene_pred :
    toNat (cAdd c2 c3) = 5 ∧
    toNat (cMul c2 c3) = 6 ∧
    toNat (cPred c3)   = 2 ∧
    toNat (cPred cZero) = 0 :=
  ⟨rfl, rfl, rfl, rfl⟩

end CursoLambda.Leccion03
```

---

## 6. Ejercicio Práctico de la Lección 03

### Ejercicio 3.1: Exponenciación de Numerales de Church ($m^n$)
En la codificación de Church, un numeral $n$ aplica una transformación $n$ veces, y multiplicar por $m$ es la transformación `cMul m`. Define la exponenciación `cExp (m n : CNat) : CNat` ($m^n$) iterando `cMul m` exactamente $n$ veces sobre el numeral $1$ (`cSucc cZero`), y demuestra por `rfl` que `toNat (cExp c2 c3) = 8` ($2^3 = 8$).

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
open CursoLambda.Leccion03

def c1 : CNat := cSucc cZero

/-- `cExp m n` calcula `m^n` aplicando `n` veces la multiplicación por `m` a partir de `1`: -/
def cExp (m n : CNat) : CNat :=
  fun α => n (α → α) (m α)

theorem church_dos_al_cubo : toNat (cExp c2 c3) = 8 := rfl
```
</details>

---

👉 **Siguiente lección:** [**Lección 04 — Lógica Combinatoria ($S, K, I, B, C, W$) y Algoritmo de Eliminación de Abstracciones (*Bracket Abstraction*)**](04_logica_combinatoria_ski_y_abstraccion.md)
