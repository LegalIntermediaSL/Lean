# Lección 04: Pruebas Transparentes zk-STARKs — Árboles de Merkle Dependientes y Plegado Polinómico FRI

> **Navegación del Mini-Curso:** [⬅️ Lección 03: Protocolos $\Sigma$ y Fiat-Shamir](03_protocolos_sigma_schnorr_y_fiat_shamir.md) | [🏠 Índice](00_indice_minicurso_zk_y_cripto.md) | [➡️ Lección 05: Criptografía Post-Cuántica LWE](05_criptografia_postcuantica_reticulos_lwe.md)
>
> **Módulos ejecutables relacionados:** [`LeanTT/M44_MerkleTreesAndCryptographicCommitments.lean`](../../LeanTT/M44_MerkleTreesAndCryptographicCommitments.lean), [`LeanTT/M55_STARKsAndFRILowDegreeFolding.lean`](../../LeanTT/M55_STARKsAndFRILowDegreeFolding.lean) y [`LeanTT/Exercises/E04_WorkoutCompilersSTARKsAndGames.lean`](../../LeanTT/Exercises/E04_WorkoutCompilersSTARKsAndGames.lean).

---

## 1. ¿En Qué se Diferencia un zk-STARK de un zk-SNARK?

Los **zk-STARKs** (*Scalable Transparent Arguments of Knowledge*, Eli Ben-Sasson et al., 2018) tienen dos ventajas fundamentales frente a los SNARKs clásicos basados en emparejamientos elípticos (como Groth16 o KZG):
1. **Son Transparentes (*Transparent*):** No requieren ninguna ceremonia de configuración confiable (*Trusted Setup*) con "residuos tóxicos" secretos. Toda la aleatoriedad es pública.
2. **Son Resistentes a Computadores Cuánticos (*Post-Quantum Secure*):** No dependen del problema del logaritmo discreto en curvas elípticas (vulnerable al algoritmo cuántico de Shor), sino únicamente de **funciones hash resistentes a colisiones** (Árboles de Merkle) y códigos correctores de errores (**Reed-Solomon / protocolo FRI**).

Un zk-STARK se construye combinando dos primitivas que tenemos formalmente verificadas en este repositorio:
1. **Árboles de Merkle Dependientemente Tipados ([`M44`](../../LeanTT/M44_MerkleTreesAndCryptographicCommitments.lean))** para comprometer evaluaciones polinómicas sobre un dominio grande.
2. **El Protocolo de Plegado Polinómico FRI ([`M55`](../../LeanTT/M55_STARKsAndFRILowDegreeFolding.lean))** para demostrar que las evaluaciones comprometidas en el Árbol de Merkle pertenecen a un polinomio de bajo grado $< d$.

---

## 2. Parte I: Árboles de Merkle Indexados por Altura (`MerkleTree h`)

En [`LeanTT/M44_MerkleTreesAndCryptographicCommitments.lean`](../../LeanTT/M44_MerkleTreesAndCryptographicCommitments.lean) utilizamos una **familia inductiva indexada por la altura `h : Nat`** para garantizar a nivel de tipos que todo árbol de Merkle está **perfectamente balanceado** ($2^h$ hojas) y que toda prueba de inclusión (`MerkleProof h`) tiene exactamente $h$ nodos hermanos:

```lean
inductive MerkleTree : Nat → Type where
  | leaf : Nat → MerkleTree 0
  | node : {h : Nat} → MerkleTree h → MerkleTree h → MerkleTree (h + 1)
```

En `M44` demostramos dos teoremas esenciales de todo esquema de compromiso vectorial:
1. **Completitud de las Pruebas de Inclusión (`verifyProof_generateProof`):** Para cualquier árbol `t : MerkleTree h` y cualquier camino de $h$ bits `path : Vec Bool h`, la prueba de inclusión generada `generateProof hash t path` reconstruye exactamente la raíz `merkleRoot hash t`.
2. **Propiedad Vinculante (*Cryptographic Binding* — `merkle_binding_or_collision`):** Si un adversario presenta dos hojas distintas `v1 ≠ v2` en la misma posición `path` con pruebas de inclusión válidas hacia la misma raíz `root`, podemos extraer constructivamente una **colisión explícita** de la función hash $H(x_1, y_1) = H(x_2, y_2)$ con $(x_1, y_1) \neq (x_2, y_2)$.

---

## 3. Parte II: El Protocolo FRI (*Fast Reed-Solomon IOP of Proximity*)

¿Cómo demuestra un Prover que un millón de valores comprometidos en un Árbol de Merkle son las evaluaciones de un polinomio de grado $< d$, haciendo que el Verificador lea solo unos pocos puntos en tiempo logarítmico $O(\log d)$?

Mediante la idea inspirada en la Transformada Rápida de Fourier (FFT) del protocolo **FRI**: **dividir el grado del polinomio a la mitad en cada ronda**.

### 3.1 La Descomposición Par-Impar y el Operador de Plegado (`friFold`)
Dado un polinomio $P(X) = c_0 + c_1 X + c_2 X^2 + c_3 X^3$ de grado $< 4$, agrupamos los monomios de exponente par y los de exponente impar:

$$P(X) \;=\; \underbrace{(c_0 + c_2 X^2)}_{P_{\text{even}}(X^2)} \;+\; X \cdot \underbrace{(c_1 + c_3 X^2)}_{P_{\text{odd}}(X^2)}$$

Observa que $P_{\text{even}}(Y) = c_0 + c_2 Y$ y $P_{\text{odd}}(Y) = c_1 + c_3 Y$ son polinomios en la variable $Y = X^2$ de **mitad de grado ($< 2$)**.
Cuando el Verificador envía un escalar aleatorio de desafío $\alpha$, el Prover define el **polinomio plegado de la siguiente ronda**:

$$P_{\text{fold}}(\alpha, Y) \;:=\; P_{\text{even}}(Y) + \alpha \cdot P_{\text{odd}}(Y)$$

### 3.2 ¿Cómo Comprueba el Verificador que el Prover ha Plegado Honestamente?
Evaluando $P(X)$ en dos puntos simétricos opuestos $\{x, -x\}$ (que tienen el mismo cuadrado $y = x^2 = (-x)^2$):
$$\begin{aligned}
P(x)  &= P_{\text{even}}(x^2) + x \cdot P_{\text{odd}}(x^2) \\
P(-x) &= P_{\text{even}}(x^2) - x \cdot P_{\text{odd}}(x^2)
\end{aligned}$$
De estas dos lecturas en el Árbol de Merkle de la ronda actual, el Verificador despeja $P_{\text{even}}(x^2)$ y $P_{\text{odd}}(x^2)$:
$$P(x) + P(-x) = 2 \cdot P_{\text{even}}(x^2) \qquad\text{y}\qquad P(x) - P(-x) = 2 \cdot x \cdot P_{\text{odd}}(x^2)$$
y comprueba en 1 operación que coinciden con el valor $P_{\text{fold}}(\alpha, x^2)$ del Árbol de Merkle de la siguiente ronda:

$$2 \cdot x \cdot P_{\text{fold}}(\alpha, x^2) \;=\; (x + \alpha) \cdot P(x) + (x - \alpha) \cdot P(-x)$$

---

## 4. Demostración en Lean 4 de la Ecuación Colineal de Verificación de Ronda de FRI

Demostremos en Lean 4 tanto las ecuaciones de descomposición como la **Ecuación Colineal de Verificación de FRI** que liga directamente $P(x)$, $P(-x)$ y $P_{\text{fold}}(\alpha, x^2)$:

```lean
import LeanTT.M55_STARKsAndFRILowDegreeFolding

namespace CursoZK.Leccion04

open LeanTT.M55

/-- TEOREMA CUMBRE DE LA LECCIÓN 04 (Ecuación Colineal de Verificación Local de FRI):
    Para todo polinomio `P : PolyDeg3`, todo desafío `α : Int` y todo punto de consulta `x : Int`,
    el valor del polinomio plegado `friFold P α` en `x²` satisface la identidad colineal exacta
    que comprueba el Verificador de un zk-STARK leyendo solo `P(x)` y `P(-x)`:
    `2 * x * P_fold(α, x²) = (x + α) * P(x) + (x - α) * P(-x)`! -/
theorem fri_collinearity_check_equation (P : PolyDeg3) (α x : Int) :
    2 * (evalDeg1 (friFold P α) (x * x) * x) =
      evalDeg3 P x * (x + α) + evalDeg3 P (-x) * (x - α) := by
  rw [eval_friFold]
  have hPos := fri_even_odd_decomposition P x
  have hNeg := fri_even_odd_decomposition P (-x)
  have hSq  : (-x) * (-x) = x * x := Int.neg_mul_neg x x
  rw [hSq, Int.mul_neg] at hNeg
  rw [hPos, hNeg]
  -- Sea `E := P_even(x²)` y `Ox := P_odd(x²) * x`:
  -- Izquierda: `2 * ((E + P_odd(x²) * α) * x) = 2 * E * x + 2 * Ox * α`
  -- Derecha:   `(E + Ox) * (x + α) + (E - Ox) * (x - α) = 2 * E * x + 2 * Ox * α`
  generalize evalDeg1 (evenPart P) (x * x) = E
  generalize evalDeg1 (oddPart P) (x * x) = O
  rw [Int.add_mul, Int.mul_right_comm O α x]
  generalize O * x = Ox
  rw [Int.mul_add 2, Int.add_mul E Ox, Int.sub_mul E Ox,
      Int.mul_add E x α, Int.mul_sub E x α,
      Int.mul_add Ox x α, Int.mul_sub Ox x α]
  omega

end CursoZK.Leccion04
```

---

## 5. Ejercicio Práctico de la Lección 04

### Ejercicio 4.1: Plegado FRI con Desafío $\alpha = -x$
Usando los teoremas del Módulo 55, demuestra en Lean 4 que si el desafío $\alpha$ coincide con $-x$, entonces evaluar el polinomio plegado `friFold P (-x)` en $x^2$ coincide exactamente con la evaluación del polinomio original en $-x$ (`evalDeg3 P (-x)`).

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
import LeanTT.M55_STARKsAndFRILowDegreeFolding

open LeanTT.M55

theorem friFold_at_neg_x (P : PolyDeg3) (x : Int) :
    evalDeg1 (friFold P (-x)) (x * x) = evalDeg3 P (-x) := by
  have h := friFold_at_x_eq_evalDeg3 P (-x)
  have hSq : (-x) * (-x) = x * x := Int.neg_mul_neg x x
  rwa [hSq] at h
```
</details>

---

👉 **Siguiente lección:** [**Lección 05 — Criptografía Post-Cuántica Basada en Retículos: *Learning With Errors* (LWE / Kyber) y Homomorfía**](05_criptografia_postcuantica_reticulos_lwe.md)
