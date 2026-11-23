/-!
# Módulo 62: Criptografía Post-Cuántica Basada en Retículos (*Learning With Errors*, LWE)
## Ámbito: Criptografía Resistente a Computadores Cuánticos (Regev 2005 / NIST ML-KEM Kyber)

La seguridad de los estándares post-cuánticos del NIST (como **ML-KEM / CRYSTALS-Kyber** y
**ML-DSA / Dilithium**) se basa en el problema **Learning With Errors (LWE)** introducido por
Oded Regev (2005, Premio Gödel 2018):
- Una clave secreta $s \in \mathbb{Z}$ se oculta publicando pares $(a, b)$ donde
  $$b = a \cdot s + e$$
  y $e \in \mathbb{Z}$ es un **ruido pequeño** ($|e| < K$).
- Para cifrar un bit $m \in \{0, 1\}$ con escala de medio-módulo $2K$ (equivalente a $\lfloor q/2 \rfloor$
  cuando $q = 4K$), el texto cifrado suma la señal codificada $m \cdot (2K)$ a la muestra ruidosa:
  $$c = a \cdot s + e + m \cdot (2K)$$
- Para descifrar conociendo la clave secreta $s$, el receptor calcula $v = c - a \cdot s = e + m \cdot (2K)$
  y decide por umbral si $v \ge K$ (bit `1`) o $v < K$ (bit `0`).

En este módulo:
1. Formalizamos la codificación del mensaje LWE, el cifrado con ruido `lweEncrypt`, la eliminación
   de máscara con la clave secreta `lweUnmask` y el decodificador por umbral `lweDecode`.
2. Demostramos el **Teorema Fundamental de Corrección de Desencriptado LWE (`lwe_decrypt_correct`)**:
   siempre que la magnitud del ruido esté acotada por el cuarto de módulo (`-K < e` y `e < K`),
   el desencriptado recupera el bit original `m : Bool` con **probabilidad 1 (cero errores)**!
3. Demostramos la **Homomorfía Aditiva del Ruido LWE** al sumar dos textos cifrados.
-/

namespace LeanTT.M62

/-- Codifica un bit `m : Bool` con separación `2 * K` (la mitad de un módulo `q = 4 * K`):
    - `false` (`0`) ↦ `0`
    - `true`  (`1`) ↦ `2 * K` -/
@[simp]
def encodeBitLWE (K : Int) (m : Bool) : Int :=
  if m then 2 * K else 0

/-- Cifrado simétrico LWE de un bit `m` bajo la clave secreta `s`, muestra pública `a` y ruido `e` -/
@[simp]
def lweEncrypt (K s a e : Int) (m : Bool) : Int :=
  a * s + e + encodeBitLWE K m

/-- Fase 1 del desencriptado LWE: sustraer el producto interno `a * s` usando la clave secreta `s` -/
@[simp]
def lweUnmask (s a c : Int) : Int :=
  c - a * s

/-- Fase 2 del desencriptado LWE (Decodificación por Umbral en `K ≈ q/4`):
    Si la señal desenmascarada `v` supera o iguala el umbral `K`, decodificamos `true` (`1`);
    en caso contrario decodificamos `false` (`0`). -/
@[simp]
def lweDecode (K v : Int) : Bool :=
  decide (K ≤ v)

/-- Desencriptado LWE completo (`lweDecrypt K s a c`) -/
@[simp]
def lweDecrypt (K s a c : Int) : Bool :=
  lweDecode K (lweUnmask s a c)

/-! ## 1. Teoremas de Cancelación de Máscara y Corrección Post-Cuántica LWE -/

/-- TEOREMA 1 (Cancelación Exacta del Término Público-Secreto `a * s`):
    Al desenmascarar `lweEncrypt K s a e m` con la clave secreta `s`, el término `a * s`
    desaparece por completo y queda únicamente `e + encodeBitLWE K m` (ruido + señal). -/
@[simp]
theorem lweUnmask_lweEncrypt (K s a e : Int) (m : Bool) :
    lweUnmask s a (lweEncrypt K s a e m) = e + encodeBitLWE K m := by
  dsimp [lweUnmask, lweEncrypt]
  omega

/-- TEOREMA 2 (Teorema Fundamental de Corrección de Desencriptado LWE con Ruido Acotado):
    Para toda escala positiva `K > 0`, toda clave secreta `s`, toda muestra pública `a`,
    todo bit `m : Bool` y todo ruido pequeño `e` que cumpla `-K < e` y `e < K` (`|e| < q/4`),
    el desencriptado LWE recupera exactamente el bit original `m`! -/
theorem lwe_decrypt_correct (K s a e : Int) (m : Bool)
    (hLow : -K < e) (hHigh : e < K) :
    lweDecrypt K s a (lweEncrypt K s a e m) = m := by
  unfold lweDecrypt
  rw [lweUnmask_lweEncrypt]
  cases m with
  | false =>
    simp only [lweDecode, encodeBitLWE, Bool.false_eq_true, ↓reduceIte, Int.add_zero,
      decide_eq_false_iff_not]
    omega
  | true =>
    simp only [lweDecode, encodeBitLWE, ↓reduceIte, decide_eq_true_eq]
    omega

/-- TEOREMA 3 (Aditividad Homomórfica de Muestras LWE):
    En criptografía homomórfica basada en retículos (BGV / BFV / TFHE), al sumar dos muestras LWE
    $(a_1, c_1)$ y $(a_2, c_2)$ bajo la misma clave secreta $s$, la señal desenmascarada de la suma
    es exactamente la suma de las señales desenmascaradas individuales (y los ruidos se suman: $e_1 + e_2$). -/
theorem lweUnmask_homomorphic_add (s a1 a2 c1 c2 : Int) :
    lweUnmask s (a1 + a2) (c1 + c2) = lweUnmask s a1 c1 + lweUnmask s a2 c2 := by
  dsimp [lweUnmask]
  rw [Int.add_mul]
  omega

end LeanTT.M62
