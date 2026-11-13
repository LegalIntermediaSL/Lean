# Módulo 11: Semántica Operacional — Paso Pequeño (*Small-Step*), Paso Grande (*Big-Step*) y Determinismo

> **Archivo Lean ejecutable asociado:** [`LeanTT/M11_OperationalSemantics.lean`](../LeanTT/M11_OperationalSemantics.lean)

---

## 1. Tres Formas de Especificar el Significado de un Lenguaje Formal

En la teoría de lenguajes de programación y del cálculo lambda, damos significado a la sintaxis mediante tres estilos complementarios:

1. **Semántica Denotacional** (vista en el Módulo 10): Traduce cada término sintáctico a un objeto matemático (una función en el metanivel).
2. **Semántica Operacional de PasoGrande (*Big-Step* / Semántica Natural de Kahn):** Define una relación inductiva $t \Downarrow v$ ("el término $t$ se evalúa directamente al valor final $v$").
3. **Semántica Operacional de Paso Pequeño (*Small-Step* / Semántica Estructural de Plotkin):** Define una relación de transición de un paso $t \longrightarrow t'$ ("$t$ da un paso de reducción hacia $t'$") y estudia su clausura reflexiva-transitiva $t \longrightarrow^* t'$.

---

## 2. Relaciones Inductivas como Reglas de Inferencia en Lean 4

Toda colección de reglas de inferencia en papel se traduce de forma biunívoca a un predicado inductivo (`inductive ... : ... → Prop`) en Lean 4. Por ejemplo, para una relación de paso pequeño `Step : Expr → Expr → Prop` (escrita `e ⟶ e'`):

$$
\frac{e_1 \longrightarrow e_1'}{\text{add } e_1\; e_2 \longrightarrow \text{add } e_1'\; e_2} \text{ (step\_add\_left)}
\qquad
\frac{v_1 \text{ es valor} \quad e_2 \longrightarrow e_2'}{\text{add } v_1\; e_2 \longrightarrow \text{add } v_1\; e_2'} \text{ (step\_add\_right)}
$$

se escribe directamente como constructores de `Step`:
```lean
inductive Step : Expr → Expr → Prop where
  | addLeft  : Step e1 e1' → Step (.add e1 e2) (.add e1' e2)
  | addRight : IsValue v1 → Step e2 e2' → Step (.add v1 e2) (.add v1 e2')
  | addVals  : Step (.add (.val n1) (.val n2)) (.val (n1 + n2))
```

---

## 3. Clausura Reflexiva-Transitiva (`MultiStep` / $\longrightarrow^*$)

Dada cualquier relación binaria $R : \alpha \to \alpha \to \texttt{Prop}$, su clausura reflexiva-transitiva $R^*$ se define inductivamente como:

```lean
inductive MultiStep (R : α → α → Prop) : α → α → Prop where
  | refl : MultiStep R x x
  | step : R x y → MultiStep R y z → MultiStep R x z
```

Propiedades metateóricas clave demostradas en [`M11_OperationalSemantics.lean`](../LeanTT/M11_OperationalSemantics.lean):
1. **Determinismo de la evaluación:** Si $e \longrightarrow e_1$ y $e \longrightarrow e_2$, entonces $e_1 = e_2$.
2. **Los valores son formas normales:** Si $v$ es un valor, no existe $e'$ tal que $v \longrightarrow e'$.
3. **Transitividad y congruencia de $\longrightarrow^*$:** Si $e_1 \longrightarrow^* e_1'$, entonces $\text{add } e_1\; e_2 \longrightarrow^* \text{add } e_1'\; e_2$.
4. **Teorema de Equivalencia entre Big-Step y Small-Step:**
   $$e \Downarrow n \;\Longleftrightarrow\; e \longrightarrow^* \text{val } n$$
