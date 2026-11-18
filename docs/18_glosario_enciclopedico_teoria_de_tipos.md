# Módulo 18: Glosario Enciclopédico de Cálculo Lambda, Teoría de Tipos Dependientes y Lean 4

Referencia alfabética de los conceptos fundamentales utilizados a lo largo de las 21 guías (`docs/00..20`), los 50 módulos ejecutables (`LeanTT/M01..M50`) y los 3 talleres prácticos (`E01..E03`).

---

### A
* **$\alpha$-Equivalencia ($\equiv_\alpha$):** Igualdad de términos que solo difieren en el nombre de sus variables ligadas ($\lambda x.\, x \equiv_\alpha \lambda y.\, y$). En el kernel de Lean es una identidad sintáctica gracias a los índices de De Bruijn.
* **Accesibilidad (`Acc r x`):** Predicado inductivo en `Prop` que afirma que no existen cadenas infinitas descendentes que partan de $x$ bajo la relación $r$. Es la base de `WellFounded.fix`.
* **Adjunción ($\alpha \dashv \gamma$ / $\Sigma_f \dashv f^* \dashv \Pi_f$):** Relación simétrica entre dos funtores o aplicaciones monótonas. En TTD, la suma dependiente $\Sigma$ es adjunta por la izquierda al cambio de base (sustitución) y el producto dependiente $\Pi$ es adjunto por la derecha (`M36`).
* **Árbol de Merkle (`MerkleTree h`):** Estructura de datos autenticada indexada por su altura $h$ que permite comprometer $2^h$ hojas en una única raíz criptográfica y verificar pertenencia en tamaño $O(h)$ (`M44`).

### B
* **$\beta$-Reducción ($\longrightarrow_\beta$):** Regla computacional fundamental que evalúa la aplicación de una abstracción lambda sustituyendo el argumento en el cuerpo: $(\lambda x.\, t)\; u \to t[x := u]$.
* **Barendregt, Cubo de ($\lambda$-Cube):** Clasificación de 8 sistemas de tipos puros según las dependencias permitidas entre términos y tipos ($\lambda^\to, \lambda 2, \lambda\underline{\omega}, \lambda\omega, \lambda P, \lambda P2, \lambda P\underline{\omega}, \lambda C$) (`M16`).
* **BHK (Interpretación de Brouwer-Heyting-Kolmogorov):** Semántica constructiva de la lógica intuicionista donde probar una proposición equivale a construir un objeto/función que certifica su verdad.

### C
* **Cálculo de Construcciones Inductivas (CIC):** El sistema formal en el que se basa Lean 4: combina $\lambda C$ con familias inductivas, una jerarquía infinita de universos `Sort u` y un universo impredicativo `Prop`.
* **Cedar (`AWS Cedar`):** Lenguaje industrial de políticas de autorización basado en los invariantes *Default Deny* y *Forbid Overrides Permit*, formalizado en Lean 4 (`M43`).
* **Church, Codificación de:** Representación de datos (booleanos, naturales, pares, listas) en el cálculo lambda puro o en el Sistema F mediante su propio iterador de orden superior (`M01`).
* **Confluencia (Propiedad de Church-Rosser):** Garantía de que si un término puede reducirse por dos caminos distintos $t \twoheadrightarrow u_1$ y $t \twoheadrightarrow u_2$, siempre existe un término común $w$ al que ambos convergen.
* **Criterio de De Bruijn:** Principio arquitectónico según el cual toda la confianza de un asistente de pruebas reside en un verificador de tipos nuclear pequeño (`M40`) independiente del elaborador (`M50`) y de las tácticas.
* **Curry-Howard, Isomorfismo de:** Correspondencia exacta entre proposiciones lógicas y tipos, demostraciones y programas ($\lambda$-términos), y simplificación de pruebas y evaluación computacional (`M04`).

### D
* **$\delta$-Reducción:** Paso de reducción en el kernel que reemplaza el nombre de una definición (`def f := e`) por su cuerpo `e`.
* **De Bruijn, Índices de:** Notación para variables ligadas donde cada variable se reemplaza por un número natural $k$ que indica cuántos ligadores ($\lambda$ o $\Pi$) hay que saltar hacia afuera hasta alcanzar su declaración (`M10`, `M40`).

### E
* **Efectos Algebraicos y Mónada Libre (`Free Monad`):** Representación de programas con efectos como árboles sintácticos de operaciones (`KVProg α`) cuya semántica es proporcionada modularmente por un intérprete o manejador (`Handler`) (`M46`).
* **Elaborador Bidireccional (`synth` $\Rightarrow$ / `check` $\Leftarrow$):** Subsistema que traduce la sintaxis de superficie del usuario (con tipos omitidos, azúcar sintáctico y metavariables `?m`) a términos completamente explícitos del Kernel (`M50`).
* **Eliminación Grande (*Large Elimination*):** Aplicación del eliminador o reconocimiento de patrones sobre un dato (como `b : Bool` o `n : Nat`) cuyo motivo devuelve un **tipo** (`Type u`) (`M13`).
* **Eliminación de Subsingletons:** Restricción que impone Lean al eliminar una proposición en `Prop` para producir un valor en `Type u`: solo se permite si el tipo inductivo en `Prop` tiene a lo sumo un constructor y sus argumentos no contienen datos ocultos (`M03`).
* **Eliminador $J$ (`Eq.rec`):** Principio de inducción sobre el tipo identidad de Martin-Löf: para probar una propiedad sobre $a, b : A$ y $p : a = b$, basta probarla para $(a, a, \texttt{rfl}_a)$ (`M06`, `M13`).

### F
* **Familia de Tipos (*Type Family*):** Función $B : A \to \texttt{Sort } u$ que asigna un tipo $B(a)$ (la *fibra*) a cada valor $a : A$ del tipo base.
* **Forma Normal de Cabeza Débil (WHNF):** Estado de una expresión tras reducirse solo hasta exponer su constructor externo ($\lambda$, $\Pi$, constructor inductivo o variable aplicada) (`M40`).

### G
* **Girard, Paradoja de:** Demostración de que un sistema de tipos dependientes o polimórficos con un único universo `Type : Type` es lógicamente inconsistente (`M03`).

### H
* **Heterogénea, Igualdad (`HEq` / `≍`):** Igualdad de John Major entre dos términos $a : \alpha$ y $b : \beta$ cuyos tipos $\alpha$ y $\beta$ no son definicionalmente iguales.
* **HoTT (Teoría de Tipos Homotópica):** Interpretación topológica de MLTT donde los tipos son $\infty$-grupoides, las pruebas de igualdad son caminos y se postula el Axioma de Univalencia en lugar de UIP (`M23`).

### I
* **$\iota$-Reducción:** Paso de reducción de un eliminador o `match` al aplicarse a un constructor concreto de un tipo inductivo.
* **Igualdad Definicional ($\equiv$) vs. Proposicional (`=`):** La igualdad definicional es verificada automáticamente por cómputo en el kernel (`rfl`); la igualdad proposicional es un tipo `a = b : Prop` que requiere una demostración explícita.
* **Impredicatividad:** Propiedad de un universo (en Lean 4, únicamente `Prop`) de permanecer cerrado bajo productos dependientes cuyos dominios viven en universos arbitrariamente altos.
* **Irrelevancia de Prueba (*Proof Irrelevance*):** Regla del kernel de Lean según la cual cualesquiera dos habitantes $p_1, p_2 : P$ de una proposición $P : \texttt{Prop}$ son definicionalmente idénticos ($p_1 \equiv p_2$).

### M
* **Metavariable (`?m`):** Hueco tipado dentro de un término o tipo parcial durante la elaboración o la ejecución de un bloque táctico `by` (`M08`, `M50`).
* **Motivo (`motive`):** La familia dependiente $C : I \to \texttt{Sort } u$ que especifica qué tipo de resultado o qué propiedad se quiere construir al eliminar o hacer inducción sobre un tipo inductivo $I$.

### N
* **No-Interferencia (*Non-Interference*):** Propiedad de seguridad según la cual las variaciones en entradas secretas (`sec`) jamás alteran los resultados observables públicos (`pub`) (`M41`).
* **Normalización por Evaluación (NbE):** Técnica que normaliza términos sintácticos evaluándolos primero en el dominio semántico del metalenguaje y reificándolos después de vuelta a sintaxis en forma normal (`M27`).

### P
* **$\Pi$-Type (Producto Dependiente `(x : A) → B x`):** Tipo de las funciones donde el tipo del valor devuelto $B(x)$ depende del valor del argumento $x : A$. Cuando $B$ es constante se reduce a $A \to B$; cuando $B(x) : \texttt{Prop}$ es el cuantificador universal $\forall x : A,\, B(x)$.
* **Positividad Estricta:** Condición exigida por el kernel en toda declaración `inductive I` según la cual `I` nunca puede aparecer a la izquierda de una flecha `→` en los tipos de los argumentos de sus constructores.
* **Protocolo $\Sigma$ (Schnorr):** Protocolo interactivo de 3 pasos $(\text{commit}, \text{challenge}, \text{response})$ que satisface Completitud, *2-Special Soundness* y *Honest-Verifier Zero-Knowledge (HVZK)* (`M42`).

### Q
* **Quórum, Intersección de:** Propiedad fundamental de los protocolos de consenso distribuido (Paxos, Raft, BFT) según la cual cualesquiera dos quórums comparten al menos un nodo honesto, impidiendo decisiones contradictorias (`M47`).

### R
* **Refinamiento, Tipo de (*Refinement Type*):** Subtipo `{ x : α // P x }` que empaqueta un valor junto con la demostración formal de su invariante lógico (`M45`).

### S
* **$\Sigma$-Type (Suma Dependiente `(x : A) × B x`):** Tipo de los pares dependientes $\langle a, b \rangle$ donde $a : A$ y $b : B(a)$. Cuando $B$ es constante se reduce al producto cartesiano $A \times B$.

### T
* **Telescopio:** Secuencia de declaraciones $(x_1 : A_1)(x_2 : A_2(x_1))\dots(x_n : A_n(x_1,\dots,x_{n-1}))$ donde el tipo de cada variable depende de las anteriores.
* **Transporte (`h ▸ px`):** Operación derivada de `Eq.rec` que convierte un habitante de la fibra $P(x)$ en un habitante de la fibra $P(y)$ a lo largo de una prueba de igualdad $h : x = y$.

### U
* **UIP (Unicidad de las Pruebas de Identidad / Axioma $K$):** Principio según el cual dos pruebas cualesquiera $p, q : x = y$ son iguales ($p = q$). En Lean 4 se cumple por `rfl` porque `x = y` vive en `Prop`.

### W
* **$W$-Type ($\mathsf{W}(a : A),\, B(a)$):** Tipo universal de árboles bien fundados de Martin-Löf parametrizado por un tipo de etiquetas de constructores $A$ y una familia de aridades $B : A \to \texttt{Type}$ (`M13`).
* **$\zeta$-Reducción:** Sustitución de una definición local `let x := v in t` por `t[x := v]`.
