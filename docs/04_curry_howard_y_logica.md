# Módulo 04: El Isomorfismo de Curry-Howard — Lógica Intuicionista vs. Lógica Clásica

> **Archivo Lean ejecutable asociado:** [`LeanTT/M04_CurryHoward.lean`](../LeanTT/M04_CurryHoward.lean)

---

## 1. La Correspondencia Proposiciones-como-Tipos (Curry-Howard-de Bruijn)

Descubierta independientemente por Haskell Curry (1934) para la lógica combinatoria y William Alvin Howard (1969) para la deducción natural de Gentzen y el cálculo lambda tipado, la correspondencia establece un **isomorfismo estructural exacto** entre sistemas lógicos y sistemas de tipos:

| Lógica Formal (Deducción Natural) | Cálculo Lambda con Tipos Dependientes | Constructores en Lean 4 | Eliminadores en Lean 4 |
| :--- | :--- | :--- | :--- |
| **Proposición** $P$ | **Tipo** $P : \texttt{Prop}$ | — | — |
| **Demostración** de $P$ | **Término** $t : P$ | — | — |
| **Implicación** $P \to Q$ | Tipo Función $P \to Q$ | Abstracción `fun (h : P) => ...` | Aplicación `f h` |
| **Conjunción** $P \land Q$ | Tipo Producto $P \times Q$ | `And.intro hp hq` / `⟨hp, hq⟩` | `h.left`, `h.right` |
| **Disyunción** $P \lor Q$ | Tipo Coproducto $P + Q$ | `Or.inl hp`, `Or.inr hq` | `Or.elim h f g` / `match` |
| **Verdad** $\top$ | Tipo Unitario $\mathbf{1}$ | `True.intro` / `trivial` | — |
| **Falsedad** $\bot$ | Tipo Vacío $\mathbf{0}$ | *(Sin constructores)* | `False.elim h` / `nomatch h` |
| **Negación** $\neg P$ | Tipo Función $P \to \bot$ | `fun (hp : P) => ...` | `hnp hp : False` |
| **Universal** $\forall x : A,\, P(x)$ | Producto Dependiente $\Pi (x : A),\, P(x)$ | `fun (x : A) => ...` | Aplicación `h a : P a` |
| **Existencial** $\exists x : A,\, P(x)$ | Suma Dependiente $\Sigma (x : A),\, P(x)$ | `Exists.intro a ha` / `⟨a, ha⟩` | `Exists.elim h (fun a ha => ...)` |
| **Simplificación de pruebas** (Eliminación de cortes) | **Reducción computacional** ($\beta/\iota$-reducción) | — | — |

---

## 2. Lógica Constructiva (Intuicionista) por Defecto

El núcleo puro del cálculo lambda tipado es **constructivo** (intuicionista):
* Una prueba constructiva de $P \lor Q$ debe ser `Or.inl hp` (sabiendo que $P$ es cierta) o `Or.inr hq` (sabiendo que $Q$ es cierta).
* Una prueba constructiva de $\exists x : A,\, P(x)$ debe proporcionar un testigo explícito $a : A$ junto con una prueba $h : P(a)$.

Por ello, en el núcleo constructivo sin axiomas adicionales, las siguientes leyes clásicas **no son demostrables en general**:
1. **Tercio Excluso (LEM):** $P \lor \neg P$
2. **Eliminación de la Doble Negación (DNE):** $\neg\neg P \to P$
3. **Ley de Peirce:** $((P \to Q) \to P) \to P$
4. **De Morgan no constructiva:** $\neg(P \land Q) \to \neg P \lor \neg Q$

### Lo que SÍ es constructivamente válido
* **Introducción de la doble negación:** $P \to \neg\neg P$ (`fun hp hnp => hnp hp`)
* **Triple negación:** $\neg\neg\neg P \leftrightarrow \neg P$
* **Contraposición directa:** $(P \to Q) \to (\neg Q \to \neg P)$
* **Tercio excluso bajo doble negación (Teorema de Glivenko):** $\neg\neg(P \lor \neg P)$ es demostrable de forma **100% constructiva**.

---

## 3. Proposiciones Decidibles (`Decidable P`) vs. Lógica Clásica (`Classical`)

Lean distingue magistralmente entre dos conceptos que la matemática informal suele mezclar:

### 3.1 `Decidable P : Type` (Computable)
```lean
class inductive Decidable (p : Prop) : Type where
  | isFalse (h : ¬p) : Decidable p
  | isTrue  (h : p)  : Decidable p
```
Nótese que `Decidable p` vive en **`Type`**, no en `Prop`. Una instancia de `Decidable p` es un **algoritmo efectivo** (booleano con prueba) que decide si $p$ se cumple o no. Esto permite escribir `if p then a else b` en programas ejecutables.

### 3.2 El Axioma de Elección (`Classical.choice`) y el Tercio Excluso (`Classical.em`)
Para razonamiento matemático clásico no constructivo, Lean incluye el axioma de Hilbert/Elección:

```lean
axiom Classical.choice {α : Sort u} : Nonempty α → α
```

Mediante el **Teorema de Diaconescu**, a partir de `Classical.choice`, la extensionalidad proposicional (`propext`) y los cocientes (`Quot`), Lean **demuestra** el principio del tercio excluso:

```lean
theorem Classical.em (p : Prop) : p ∨ ¬p
```

> **Advertencia sobre `noncomputable`:** Como `Classical.choice` es un axioma sin regla de reducción computacional, cualquier función que devuelva datos en `Type` haciendo distinción de casos sobre un hecho puramente clásico (no decidible algorítmicamente) debe marcarse como `noncomputable def`. Sin embargo, las demostraciones de teoremas (`theorem ... : P` con $P : \texttt{Prop}$) pueden usar `Classical.em` libremente sin afectar a la compilación.
