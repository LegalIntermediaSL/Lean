# Cuaderno 01: Del Papel al Lean Infoview — Tu Primera Demostración Fotograma a Fotograma

> **Jupyter Notebook (`.ipynb`) correspondiente:** [`notebooks/01_del_papel_al_infoview_paso_a_paso.ipynb`](../../notebooks/01_del_papel_al_infoview_paso_a_paso.ipynb)
> **Navegación:** [⬅ Índice de Cuadernos](00_indice_cuadernos_demostracion_e_ia.md) | [Siguiente: Cuaderno 02 (Nicómaco y `calc`) ➡](02_cuaderno_induccion_nicomaco_y_calc.md)

---

## 🎯 Objetivo del Cuaderno

Ver con lupa qué ocurre dentro de **Lean 4** en cada línea cuando demostramos dos teoremas fundamentales:
1. Un teorema **lógico** de distribución condicional: $(P \land (Q \lor R)) \to ((P \land Q) \lor (P \land R))$.
2. Un teorema **aritmético con cuantificador existencial**: *la suma de dos números impares cualesquiera es siempre un número par*.

En cada celda verás:
* La **intuición en papel**.
* La **radiografía exacta del Lean Infoview** ($\Gamma \vdash G$) antes y después de cada táctica.
* El **término $\lambda$ puro** que las tácticas construyen por debajo para el Kernel (`#print`).

---

## Celda 1 — Demostración Lógica Fotograma a Fotograma (`intro`, `rcases`, `left`/`right`, `exact`)

En papel diríamos: *"Supongamos que se cumple $P$ y además se cumple $Q$ o $R$. Separamos en dos casos: si se cumple $Q$, tenemos $P \land Q$ (lado izquierdo); si se cumple $R$, tenemos $P \land R$ (lado derecho)"*.

Observa cómo cada frase en castellano se convierte **uno a uno** en una táctica de Lean 4:

```lean
namespace Cuaderno01

theorem distrib_and_or (P Q R : Prop) :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R) := by
  -- [Fotograma 0] Meta inicial:
  --   P Q R : Prop
  --   ⊢ P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)

  -- Frase 1: "Supongamos la hipótesis antecedente `h : P ∧ (Q ∨ R)`"
  intro h
  -- [Fotograma 1] Tras `intro h`:
  --   h : P ∧ (Q ∨ R)
  --   ⊢ (P ∧ Q) ∨ (P ∧ R)

  -- Frase 2: "Descomponemos `h` en `hp : P` y en los dos casos `hq : Q` o `hr : R`"
  rcases h with ⟨hp, hq | hr⟩
  · -- [Fotograma 2a - Submeta Caso 1]
    --   hp : P,  hq : Q
    --   ⊢ (P ∧ Q) ∨ (P ∧ R)
    left
    -- [Fotograma 3a] Tras elegir el lado izquierdo con `left`:
    --   ⊢ P ∧ Q
    exact ⟨hp, hq⟩
  · -- [Fotograma 2b - Submeta Caso 2]
    --   hp : P,  hr : R
    --   ⊢ (P ∧ Q) ∨ (P ∧ R)
    right
    exact ⟨hp, hr⟩

-- Inspeccionemos el programa funcional (término λ) que Lean ha generado para el Kernel!
#print distrib_and_or

end Cuaderno01
```

---

## Celda 2 — La Misma Demostración Escrita Directamente como un Programa Funcional (Modo Término)

Como por Curry-Howard `∧` es un par ordenado y `∨` es un tipo suma con constructores `Or.inl` y `Or.inr`, podemos escribir la demostración anterior **sin bloque `by`**, mediante `match`:

```lean
namespace Cuaderno01

theorem distrib_and_or_termino (P Q R : Prop) :
    P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
  | ⟨hp, Or.inl hq⟩ => Or.inl ⟨hp, hq⟩
  | ⟨hp, Or.inr hr⟩ => Or.inr ⟨hp, hr⟩

-- En Prop, cualesquiera dos demostraciones del mismo teorema son iguales (Proof Irrelevance!):
example (P Q R : Prop) :
    distrib_and_or P Q R = distrib_and_or_termino P Q R := rfl

end Cuaderno01
```

---

## Celda 3 — Demostración Aritmética con Testigos (`∃`): Suma de Dos Impares = Par

1. **Formalización de conceptos:**
   * `EsPar n` significa $\exists k : \mathbb{N},\, n = 2k$.
   * `EsImpar n` significa $\exists k : \mathbb{N},\, n = 2k + 1$.
2. **Estrategia:**
   * Si $a = 2 k_1 + 1$ y $b = 2 k_2 + 1$, entonces $a + b = 2(k_1 + k_2 + 1)$.
   * Por tanto, el **testigo constructivo** que debemos entregar al cuantificador existencial $\exists k$ es exactamente `k1 + k2 + 1`!

```lean
namespace Cuaderno01

def EsPar   (n : Nat) : Prop := ∃ k : Nat, n = 2 * k
def EsImpar (n : Nat) : Prop := ∃ k : Nat, n = 2 * k + 1

theorem suma_impares_es_par {a b : Nat} (ha : EsImpar a) (hb : EsImpar b) :
    EsPar (a + b) := by
  -- 1. Extraemos los testigos `k1` y `k2` junto con sus ecuaciones `ha_eq` y `hb_eq`:
  rcases ha with ⟨k1, ha_eq⟩
  rcases hb with ⟨k2, hb_eq⟩
  -- [Infoview actual]:
  --   a b k1 k2 : Nat
  --   ha_eq : a = 2 * k1 + 1
  --   hb_eq : b = 2 * k2 + 1
  --   ⊢ EsPar (a + b)   (es decir, `∃ k, a + b = 2 * k`)

  -- 2. Proporcionamos el testigo explícito `k := k1 + k2 + 1` con `refine ⟨testigo, ?_⟩`:
  refine ⟨k1 + k2 + 1, ?_⟩
  -- [Infoview tras entregar el testigo]:
  --   ⊢ a + b = 2 * (k1 + k2 + 1)

  -- 3. Como ahora la meta es aritmética lineal pura sobre Nat, `omega` la cierra al instante:
  omega

#print axioms suma_impares_es_par

end Cuaderno01
```

---

## 📝 Resumen de Aprendizajes del Cuaderno 01
* **`intro`** mueve premisas `A → ...` o variables `∀ x, ...` desde la meta hacia arriba de `⊢`.
* **`rcases`** abre hipótesis `∧`, `∨` y `∃` que ya están en tu contexto.
* **`refine ⟨testigo, ?_⟩`** propone el testigo concreto para demostrar una meta existencial `∃ k, P k` y deja pendiente únicamente la submeta `P testigo`.
* **`#print` y `#print axioms`** confirman el término verificado por el kernel.

👉 **Siguiente cuaderno:** [**Cuaderno 02 — Inducción, Blueprints y Cadenas Ecuacionales `calc`: El Teorema de Nicómaco**](02_cuaderno_induccion_nicomaco_y_calc.md)
