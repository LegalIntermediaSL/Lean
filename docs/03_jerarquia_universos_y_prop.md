# Módulo 03: Jerarquía de Universos (`Sort u`), `Prop`, Impredicatividad y la Paradoja de Girard

> **Archivo Lean ejecutable asociado:** [`LeanTT/M03_UniversesAndProp.lean`](../LeanTT/M03_UniversesAndProp.lean)

---

## 1. ¿Por qué no puede existir `Type : Type`? La Paradoja de Girard

En una teoría de tipos dependientes donde los tipos son términos, todo tipo debe tener a su vez un tipo (llamado un **universo** o **sort**). La tentación inmediata es postular un único universo universal $\mathcal{U}$ que se contenga a sí mismo:

$$\mathcal{U} : \mathcal{U}$$

En 1972, **Jean-Yves Girard** demostró que añadir $\mathcal{U} : \mathcal{U}$ al cálculo lambda polimórfico permite reproducir la paradoja de Burali-Forti / Russell (conocida como **Paradoja de Girard**), haciendo que el tipo vacío $\bot$ (`False`) sea habitable y destruyendo la consistencia lógica del sistema.

---

## 2. La Jerarquía Estratificada de Universos `Sort u`

Para evitar la autorreferencia circular, Lean estratifica los universos en una jerarquía infinita indexada por niveles de universo $u \in \mathbb{N}$:

$$
\begin{aligned}
\texttt{Prop} &\equiv \texttt{Sort 0} \\
\texttt{Type} \equiv \texttt{Type 0} &\equiv \texttt{Sort 1} \\
\texttt{Type 1} &\equiv \texttt{Sort 2} \\
\texttt{Type } u &\equiv \texttt{Sort }(u + 1)
\end{aligned}
$$

Cada universo es un término del universo inmediatamente superior:

$$\texttt{Prop} : \texttt{Type 0} : \texttt{Type 1} : \texttt{Type 2} : \dots$$

> **Nota sobre cumulatividad:** A diferencia de Coq/Rocq, **Lean no tiene subtipado acumulativo** implícito entre universos (`α : Type 0` no tiene automáticamente tipo `Type 1`). En su lugar, Lean proporciona el elevador explícito `ULift.{v, u} α : Type (max u v)` y un sistema muy flexible de **polimorfismo de universos** (`universe u v`).

---

## 3. La Regla del Universo de los $\Pi$-Types y la Función $\text{imax}$

Si tenemos un dominio $A : \texttt{Sort } u$ y un codominio dependiente $B : A \to \texttt{Sort } v$, ¿en qué universo vive el tipo producto dependiente $(x : A) \to B(x)$?

Vive en $\texttt{Sort }(\text{imax}(u, v))$, donde la función $\text{imax}$ se define como:

$$
\text{imax}(u, v) = \begin{cases}
0 & \text{si } v = 0 \\
\max(u, v) & \text{si } v > 0
\end{cases}
$$

Esta definición captura simultáneamente dos propiedades fundamentales:

### 3.1 Predicatividad de `Type u` ($v > 0$)
Si el codominio es un tipo de datos ($v = v' + 1 > 0$), entonces $\text{imax}(u, v) = \max(u, v)$. Por ejemplo:
* `Nat → Bool` vive en `Type 0` ($\max(1, 1) = 1$).
* `Type 0 → Nat` vive en `Type 1` ($\max(2, 1) = 2$), porque cuantifica sobre `Type 0`, que vive en `Type 1`.

### 3.2 Impredicatividad de `Prop` ($v = 0$)
Si el codominio es una proposición lógica ($B(x) : \texttt{Prop} = \texttt{Sort 0}$), entonces $v = 0$ y por tanto **$\text{imax}(u, 0) = 0$ para cualquier $u$**.

Esto significa que una proposición que cuantifica sobre **todos los tipos** o incluso sobre el propio `Prop`:

$$(\forall P : \texttt{Prop},\, P \to P) : \texttt{Prop}$$
$$(\forall \alpha : \texttt{Type 5},\, \forall x : \alpha,\, x = x) : \texttt{Prop}$$

¡sigue teniendo tipo `Prop` (`Sort 0`)! Decimos que **`Prop` es impredicativo**.

---

## 4. Irrelevancia de Prueba (*Proof Irrelevance*)

En Lean 4, el universo `Prop` representa afirmaciones lógicas cuyo único contenido relevante es si están habitadas o no. Para cualquier proposición $P : \texttt{Prop}$ y cualesquiera dos pruebas $p, q : P$, el kernel de Lean impone **definicionalmente**:

$$p \equiv q$$

Por tanto, el teorema de irrelevancia de prueba se demuestra por simple reflexividad (`rfl`):

```lean
theorem proof_irrel {P : Prop} (p q : P) : p = q := rfl
```

---

## 5. Eliminación Restringida de `Prop` hacia `Type` (*Large Elimination*)

Si `Prop` es impredicativo y además tiene irrelevancia de prueba, permitir extraer datos arbitrarios de una prueba en `Prop` para construir un valor en `Type` conduciría a una contradicción (Teorema de Coquand): si existieran dos pruebas $p_1, p_2 : P$ que se redujeran a `true` y `false` en `Bool`, tendríamos `true = false` por irrelevancia de prueba.

Por ello, Lean **prohíbe eliminar un tipo inductivo en `Prop` para producir un valor en `Type u`**, **salvo** cuando la proposición es un **subsingleton sintáctico**, es decir, cumple:
1. Tiene **a lo sumo un constructor** (por ejemplo, `False` tiene 0 constructores; `True`, `And` y `Eq` tienen 1 constructor).
2. Todos los argumentos de ese constructor que contienen datos no proposicionales están fijados como índices o son ellos mismos proposiciones en `Prop`.

> **Consecuencia fundamental:** No puedes hacer `match` sobre una prueba de `P ∨ Q` (que tiene dos constructores: `Or.inl` y `Or.inr`) ni de `∃ x : Nat, P x` (cuyo testigo `x : Nat` vive en `Type`) para devolver un `Nat`. En cambio, **sí** puedes eliminar `False` (`False.elim : False → α`), `And` (`h.left`, `h.right`) y `Eq` (`Eq.rec`, transporte de tipos) hacia cualquier `Sort u`.
