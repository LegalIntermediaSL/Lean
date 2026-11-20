/-!
# Módulo 56: Teoría de Juegos Algorítmica, Equilibrio de Nash y Subasta de Segundo Precio de Vickrey
## Ámbito: Diseño de Mecanismos Económicos (VCG), Subastas de Blockchain y Estrategias Dominantes

La **Teoría de Juegos Algorítmica** y el **Diseño de Mecanismos** (William Vickrey 1961, Premio Nobel 1996)
son esenciales en protocolos descentralizados, subastas de espacio de bloques (MEV / EIP-1559)
y mercados computacionales.

En este módulo:
1. Formalizamos la **Subasta de Sobre Cerrado de Segundo Precio de Vickrey** entre dos licitadores:
   - Quien puja más alto gana el bien, pero **paga la puja del segundo más alto** (la puja del rival).
   - La utilidad cuasilineal del Jugador 1 con valoración privada verdadera `v1 : Int` cuando puja `b1`
     frente a la puja rival `b2` es:
     - `v1 - b2` si `b1 ≥ b2` (gana la subasta y paga `b2`)
     - `0`       si `b1 < b2` (pierde la subasta y paga `0`).
2. Demostramos formalmente el **Teorema de Veracidad (Incentive Compatibility / DSIC) de Vickrey**:
   Pujar la verdadera valoración privada (`b1 = v1`) es una **estrategia débilmente dominante**
   para cualquier valoración `v1`, cualquier puja rival `b2` y cualquier puja alternativa mentirosa `b1'`!
-/

namespace LeanTT.M56

/-- Utilidad del Jugador 1 en una Subasta de Segundo Precio de Vickrey:
    - `v1` : valoración real privada del Jugador 1 por el objeto.
    - `b1` : puja declarada por el Jugador 1.
    - `b2` : puja del oponente (Jugador 2). -/
@[simp]
def vickreyUtility (v1 b1 b2 : Int) : Int :=
  if b2 ≤ b1 then v1 - b2 else 0

/-! ## 1. Propiedades de No-Negatividad e Individual Rationality -/

/-- TEOREMA 1 (Racionalidad Individual / Utilidad No Negativa de la Puja Verdadera):
    Si un jugador puja su valoración verdadera `b1 = v1`, ¡su utilidad en la subasta de Vickrey
    NUNCA puede ser negativa (`0 ≤ vickreyUtility v1 v1 b2`), independientemente de lo que puje el rival! -/
theorem vickrey_individual_rationality (v1 b2 : Int) :
    0 ≤ vickreyUtility v1 v1 b2 := by
  dsimp [vickreyUtility]
  split <;> omega

/-! ## 2. El Teorema de Vickrey (1961): Pujar la Verdad es Estrategia Dominante (DSIC) -/

/-- TEOREMA 2 (Teorema Fundamental de Vickrey — *Dominant-Strategy Incentive Compatibility*):
    Para cualquier valoración verdadera `v1 : Int`, cualquier puja del oponente `b2 : Int` y
    CUALQUIER puja alternativa `b1' : Int` (sea sobrepuja `b1' > v1` o infrapuja `b1' < v1`),
    la utilidad de decir la verdad (`b1 = v1`) es siempre mayor o igual que la utilidad de pujar `b1'`:
    `vickreyUtility v1 b1' b2 ≤ vickreyUtility v1 v1 b2`. -/
theorem vickrey_truthful_dominant (v1 b1' b2 : Int) :
    vickreyUtility v1 b1' b2 ≤ vickreyUtility v1 v1 b2 := by
  dsimp [vickreyUtility]
  split <;> split <;> omega

/-! ## 3. Análisis Formal del Dilema del Prisionero y Equilibrio de Nash Estricto -/

/-- Acciones en el Dilema del Prisionero: Cooperar (`coop`) o Traicionar/Desertar (`defect`) -/
inductive ActionPD where
  | coop   : ActionPD
  | defect : ActionPD
  deriving Repr, DecidableEq

/-- Pago (utilidad) del Jugador 1 en el Dilema del Prisionero clásico (`T > R > P > S`: `5 > 3 > 1 > 0`): -/
@[simp]
def payoffPD (a1 a2 : ActionPD) : Nat :=
  match a1, a2 with
  | .coop,   .coop   => 3 -- Recompensa por cooperación mutua (R = 3)
  | .coop,   .defect => 0 -- Pago del ingenuo (S = 0)
  | .defect, .coop   => 5 -- Tentación de traicionar (T = 5)
  | .defect, .defect => 1 -- Castigo por traición mutua (P = 1)

/-- TEOREMA 3: En el Dilema del Prisionero de una sola ronda, `.defect` domina estrictamente
    a `.coop` frente a cualquier acción `a2` del otro jugador. -/
theorem prisoner_dilemma_defect_strictly_dominates (a2 : ActionPD) :
    payoffPD .coop a2 < payoffPD .defect a2 := by
  cases a2 <;> decide

end LeanTT.M56
