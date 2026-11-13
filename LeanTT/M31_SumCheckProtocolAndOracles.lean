/-!
# Módulo 31: El Protocolo Sum-Check y Reducciones de Oráculo (Inspirado en `ArkLib` y `VCV-io`)
## Ámbito: Pruebas Interactivas (IP), SNARKs y Criptografía Verificada

El protocolo **Sum-Check** (Lund, Fortnow, Karloff, Nisan, 1992) es la piedra angular de los
SNARKs modernos (y el corazón de **ArkLib** de `Verified-zkEVM`).
Permite que un *Prover* convenza a un *Verifier* de que la suma de un polinomio $g(x_1, x_2)$
sobre el hipercubo booleano $\{0, 1\}^2$:
$$H = \sum_{b_1 \in \{0,1\}} \sum_{b_2 \in \{0,1\}} g(b_1, b_2)$$
es correcta sin que el Verifier tenga que evaluar toda la suma exponencial, reduciendo la
afirmación mediante desafíos aleatorios $r_1, r_2$ a una única evaluación de oráculo $g(r_1, r_2)$.

En este módulo formalizamos una ronda y el protocolo completo de 2 variables y demostramos su
**Completitud Perfecta (*Perfect Completeness*)**: si el Prover es honesto, el Verifier
acepta para **cualquier** elección de desafíos aleatorios $r_1, r_2 \in \mathbb{Z}$.
-/

namespace LeanTT.M31

/-- Polinomio bivariado representado como función `Int → Int → Int` -/
abbrev Poly2 := Int → Int → Int

/-- Polinomio univariado enviado por el Prover en cada ronda (`Int → Int`) -/
abbrev Poly1 := Int → Int

/-- La suma verdadera de `g` sobre el hipercubo booleano `{0, 1} × {0, 1}` -/
def hypercubeSum2 (g : Poly2) : Int :=
  g 0 0 + g 0 1 + g 1 0 + g 1 1

/-- El mensaje honesto del Prover en la Ronda 1:
    el polinomio univariado `s1(X₁) = g(X₁, 0) + g(X₁, 1)`. -/
def honestRound1Poly (g : Poly2) : Poly1 :=
  fun x1 => g x1 0 + g x1 1

/-- El mensaje honesto del Prover en la Ronda 2 (tras recibir el desafío `r1` del Verifier):
    el polinomio univariado `s2(X₂) = g(r1, X₂)`. -/
def honestRound2Poly (g : Poly2) (r1 : Int) : Poly1 :=
  fun x2 => g r1 x2

/-- Las 3 comprobaciones que ejecuta el Verifier del protocolo Sum-Check con desafíos `(r1, r2)`:
    1. Ronda 1: `s1(0) + s1(1) = claimedSum`
    2. Ronda 2: `s2(0) + s2(1) = s1(r1)`
    3. Consulta final al oráculo de `g`: `s2(r2) = g(r1, r2)` -/
def sumCheckVerifier (g : Poly2) (claimedSum : Int)
    (s1 s2 : Poly1) (r1 r2 : Int) : Prop :=
  (s1 0 + s1 1 = claimedSum) ∧
  (s2 0 + s2 1 = s1 r1) ∧
  (s2 r2 = g r1 r2)

/-- TEOREMA DE COMPLETITUD PERFECTA (*Perfect Completeness*) DEL PROTOCOLO SUM-CHECK:
    Para cualquier polinomio `g` y cualesquiera desafíos `r1, r2 : Int` elegidos por el
    Verifier, los polinomios del Prover honesto hacen que `sumCheckVerifier` acepte siempre! -/
theorem sumCheck_completeness (g : Poly2) (r1 r2 : Int) :
    sumCheckVerifier g (hypercubeSum2 g)
      (honestRound1Poly g)
      (honestRound2Poly g r1)
      r1 r2 := by
  dsimp [sumCheckVerifier, hypercubeSum2, honestRound1Poly, honestRound2Poly]
  refine ⟨?_, rfl, rfl⟩
  omega

/-- Demostración de detección en Ronda 1: Si el Prover afirma una suma falsa `claimedSum ≠ hypercubeSum2 g`
    pero envía el polinomio honesto `s1`, la primera ecuación del Verifier rechaza inmediatamente. -/
theorem sumCheck_rejects_wrong_sum (g : Poly2) (claimedSum : Int) (s2 : Poly1) (r1 r2 : Int)
    (h_wrong : claimedSum ≠ hypercubeSum2 g) :
    ¬ sumCheckVerifier g claimedSum (honestRound1Poly g) s2 r1 r2 := by
  intro ⟨h1, _, _⟩
  apply h_wrong
  dsimp [honestRound1Poly, hypercubeSum2] at h1 ⊢
  omega

end LeanTT.M31
