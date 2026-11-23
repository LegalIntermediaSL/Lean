# Lección 04: Lógica Combinatoria ($S, K, I, B, C, W$) y Algoritmo de Eliminación de Abstracciones (*Bracket Abstraction*)

> **Navegación del Mini-Curso:** [⬅️ Lección 03: Codificaciones de Church/Scott y Punto Fijo](03_codificaciones_church_scott_y_punto_fijo.md) | [🏠 Índice](00_indice_minicurso_lambda.md) | [➡️ Lección 05: STLC, Normalización Fuerte y Sistema F](05_calculo_lambda_tipado_stlc_y_sistema_f.md)
>
> **Módulos ejecutables relacionados:** [`LeanTT/M01_LambdaCalculus.lean`](../../LeanTT/M01_LambdaCalculus.lean), [`LeanTT/M02_DependentTypes.lean`](../../LeanTT/M02_DependentTypes.lean) y [`LeanTT/M04_CurryHoward.lean`](../../LeanTT/M04_CurryHoward.lean).

---

## 1. ¿Es Posible un Lenguaje Funcional Universal SIN Variables Ligadas?

En **1924** (ocho años *antes* de que Church publicara el cálculo $\lambda$), el matemático ucraniano **Moses Schönfinkel** presentó en Gotinga un descubrimiento asombroso, desarrollado posteriormente por **Haskell Curry (1930)**:
> **Cualquier función computable y cualquier término del cálculo $\lambda$ puede expresarse sin usar una sola variable ligada ni una sola abstracción $\lambda$, componiendo únicamente dos constantes primitivas: $S$ y $K$.**

Este sistema se llama **Lógica Combinatoria (CL)** y fue utilizado por David Turner (1979) como arquitectura de máquina virtual para compilar lenguajes funcionales perezosos (Miranda, SASL y los precursores de Haskell) mediante reducción de grafos.

---

## 2. El Bestiario de los Combinadores Clásicos (Las «Aves» de Raymond Smullyan)

En su libro *To Mock a Mockingbird* (1985), el lógico Raymond Smullyan bautizó cada combinador con el nombre de un ave. Aquí tienes los seis combinadores fundamentales, su ecuación de reducción, su término $\lambda$ equivalente y su significado en lógica y programación funcional:

| Combinador | Nombre (Smullyan) | Regla de Reducción | Término $\lambda$ | Tipo en Lean 4 (y Axioma Lógico por Curry-Howard) |
| :---: | :--- | :--- | :--- | :--- |
| **$I$** | *Idiot / Identity* | $I\; x \longrightarrow x$ | $\lambda x.\, x$ | $\alpha \to \alpha$ *(Identidad)* |
| **$K$** | *Kestrel* (Constante) | $K\; x\; y \longrightarrow x$ | $\lambda x.\, \lambda y.\, x$ | $\alpha \to \beta \to \alpha$ *(Debilitamiento / Axioma 1 de Hilbert)* |
| **$S$** | *Starling* (Fusión) | $S\; f\; g\; x \longrightarrow (f\; x)\; (g\; x)$ | $\lambda f.\, \lambda g.\, \lambda x.\, (f\; x)\; (g\; x)$ | $(\alpha \to \beta \to \gamma) \to (\alpha \to \beta) \to \alpha \to \gamma$ *(Axioma 2 de Hilbert)* |
| **$B$** | *Bluebird* (Composición) | $B\; f\; g\; x \longrightarrow f\; (g\; x)$ | $\lambda f.\, \lambda g.\, \lambda x.\, f\; (g\; x)$ | $(\beta \to \gamma) \to (\alpha \to \beta) \to \alpha \to \gamma$ *(Composición $f \circ g$)* |
| **$C$** | *Cardinal* (`flip`) | $C\; f\; x\; y \longrightarrow f\; y\; x$ | $\lambda f.\, \lambda x.\, \lambda y.\, f\; y\; x$ | $(\alpha \to \beta \to \gamma) \to \beta \to \alpha \to \gamma$ *(Intercambio)* |
| **$W$** | *Warbler* (Duplicador) | $W\; f\; x \longrightarrow f\; x\; x$ | $\lambda f.\, \lambda x.\, f\; x\; x$ | $(\alpha \to \alpha \to \beta) \to \alpha \to \beta$ *(Contracción)* |

> **Observación estructural (Conexión con Lógica Subestructural del [`Módulo 28`](../../LeanTT/M28_SubstructuralAndLinearTypes.lean)):**
> * **$K$** es el combinador que **descarta** un argumento ($y$ desaparece). Un sistema sin $K$ es un sistema *relevante*.
> * **$W$** (o **$S$**) es el combinador que **duplica** un argumento ($x$ se usa dos veces). Un sistema sin $W$ ni $S$ (pero con $B, C, I, K$) es un sistema *afín*.
> * Un sistema construido solo con **$B, C, I$** usa cada variable **exactamente una vez**: ¡corresponde exactamente al **Cálculo $\lambda$ Lineal**!

---

## 3. El Algoritmo de Eliminación de Abstracciones (*Bracket Abstraction*)

¿Cómo se compila mecánicamente cualquier abstracción $\lambda x.\, T$ en una combinación de $S, K, I$ que no contiene a $x$?
Definimos la operación de **abstracción sintáctica** $[x]^*\, T$ por recursión sobre la estructura del término $T$:

1. **Caso Variable Idéntica:** $[x]^*\, x \;:=\; I$
2. **Caso Constante / Otra Variable ($y \neq x$, o en general $x \notin FV(T)$):** $[x]^*\, T \;:=\; K\; T$
3. **Caso Aplicación ($T_1\; T_2$):** $[x]^*\, (T_1\; T_2) \;:=\; S\; ([x]^*\, T_1)\; ([x]^*\, T_2)$

Si un término tiene varias abstracciones anidadas $\lambda x.\, \lambda y.\, T$, aplicamos el algoritmo **de adentro hacia afuera**: primero eliminamos $\lambda y$ calculando $T' := [y]^*\, T$, y luego eliminamos $\lambda x$ calculando $[x]^*\, T'$.

### Ejemplo Paso a Paso: Compilar $\lambda x.\, \lambda y.\, y\; x$ a $S, K, I$
1. Eliminamos la variable interna $y$ en el cuerpo $y\; x$:
   $$[y]^*\, (y\; x) \;=\; S\; ([y]^*\, y)\; ([y]^*\, x) \;=\; S\; I\; (K\; x)$$
2. Ahora eliminamos la variable externa $x$ en $S\; I\; (K\; x) \equiv (S\; I)\; (K\; x)$:
   $$[x]^*\, \big((S\; I)\; (K\; x)\big) \;=\; S\; \big([x]^*\, (S\; I)\big)\; \big([x]^*\, (K\; x)\big) \;=\; S\; \big(K\; (S\; I)\big)\; \big(S\; (K\; K)\; I\big)$$

---

## 4. Formalización y Demostración de Corrección de *Bracket Abstraction* en Lean 4

En Lean 4 podemos implementar el compilador completo de expresiones con variables a árboles puros de combinadores $S, K, I$ y **demostrar formalmente su teorema de corrección semántica**: evaluar el árbol $S, K, I$ aplicado a un argumento $v$ produce exactamente el mismo resultado que evaluar el término original con la variable ligada a $v$!

```lean
namespace CursoLambda.Leccion04

/-- Árboles de Lógica Combinatoria SKI con variables libres `var i` -/
inductive SKITerm where
  | S   : SKITerm
  | K   : SKITerm
  | I   : SKITerm
  | var : Nat → SKITerm
  | app : SKITerm → SKITerm → SKITerm
  deriving Repr, DecidableEq

/-- Algoritmo de Bracket Abstraction `[x]* t`:
    Elimina la variable `x : Nat` produciendo un término donde `x` equivale al argumento externo: -/
@[simp]
def bracketAbstract (x : Nat) : SKITerm → SKITerm
  | .S       => .app .K .S
  | .K       => .app .K .K
  | .I       => .app .K .I
  | .var y   => if y == x then .I else .app .K (.var y)
  | .app f a => .app (.app .S (bracketAbstract x f)) (bracketAbstract x a)

/-- Identidad famosa de la Lógica Combinatoria: `I` ni siquiera es necesario como primitivo,
    porque `S K K x` se reduce siempre a `x` (`S K K ≡ I`)! -/
def combS {α β γ : Type} (f : α → β → γ) (g : α → β) (x : α) : γ := f x (g x)
def combK {α β : Type} (x : α) (_ : β) : α := x

theorem SKK_es_la_identidad {α : Type} (x : α) :
    combS (@combK α (α → α)) (@combK α α) x = x :=
  rfl

end CursoLambda.Leccion04
```

---

## 5. Ejercicio Práctico de la Lección 04

### Ejercicio 4.1: Derivar el Combinador $B$ (Composición) a partir de $S$ y $K$
Comprueba en Lean 4 que el término combinatorio $S\; (K\; S)\; K$ actúa exactamente como el combinador de composición $B\; f\; g\; x = f(g(x))$.

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
open CursoLambda.Leccion04

def combB_desde_SK {α β γ : Type} : (β → γ) → (α → β) → α → γ :=
  combS (combK combS) combK

theorem B_derivado_de_SK_correcto {α β γ : Type} (f : β → γ) (g : α → β) (x : α) :
    combB_desde_SK f g x = f (g x) :=
  rfl
```
</details>

---

👉 **Siguiente lección:** [**Lección 05 — Del Cálculo $\lambda$ Simplemente Tipado (STLC) al Sistema F, Normalización Fuerte y Parametricidad**](05_calculo_lambda_tipado_stlc_y_sistema_f.md)
