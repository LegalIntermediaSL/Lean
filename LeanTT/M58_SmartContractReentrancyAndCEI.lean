/-!
# Módulo 58: Seguridad de Smart Contracts II — Ataques de Reentrancia y el Patrón *Checks-Effects-Interactions* (CEI)
## Ámbito: Verificación Formal de Contratos Inteligentes (EVM / Solidity) y Prevención del Exploit *The DAO*

En el famoso ataque a *The DAO* (2016), un contrato actualizaba el balance del usuario **después**
de enviarle los fondos mediante una llamada externa (`call`). El atacante re-entraba recursivamente
en `withdraw` antes de que su balance se pusiera a `0`, vaciando toda la bóveda del contrato.

La defensa estándar en Solidity y `evm-asm` es:
1. El patrón **Checks-Effects-Interactions (CEI)**: comprobar primero la condición (`bal ≥ amount`),
   aplicar **inmediatamente el efecto sobre el estado** (`bal := bal - amount`, `vault := vault - amount`)
   antes de cualquier interacción externa.
2. Un cerrojo de exclusión mutua (**ReentrancyGuard / `locked : Bool`**) que rechaza cualquier llamada
   mientras otra ejecución está en curso.
-/

namespace LeanTT.M58

/-- Estado de un contrato de bóveda (*Vault*) -/
structure VaultState where
  vault     : Nat  -- Fondos totales depositados en el contrato
  userBal   : Nat  -- Saldo acreditado al usuario actual
  withdrawn : Nat  -- Total retirado exitosamente por el usuario
  locked    : Bool -- Cerrojo `ReentrancyGuard` (`true` durante una interacción externa)
  deriving Repr, DecidableEq

/-- Invariante de Solvencia de la Bóveda: el contrato siempre tiene fondos suficientes
    para cubrir el saldo acreditado al usuario (`userBal ≤ vault`). -/
def IsSolvent (s : VaultState) : Prop :=
  s.userBal ≤ s.vault

/-- Fase 1 + 2 del Patrón CEI (*Checks-Effects*) con `ReentrancyGuard`:
    1. CHECK: Comprueba que el contrato NO está bloqueado (`s.locked = false`) y que `amount ≤ s.userBal` y `amount ≤ s.vault`.
    2. EFFECT: Descuenta `amount` de `userBal` y `vault` ANTES de la interacción externa y activa `locked := true`. -/
@[simp]
def beginWithdrawCEI (s : VaultState) (amount : Nat) : VaultState :=
  if s.locked then
    s
  else if amount ≤ s.userBal ∧ amount ≤ s.vault then
    { vault     := s.vault - amount
    , userBal   := s.userBal - amount
    , withdrawn := s.withdrawn + amount
    , locked    := true }
  else
    s

/-- Liberación del cerrojo al terminar la interacción externa -/
@[simp]
def endWithdrawCEI (s : VaultState) : VaultState :=
  { s with locked := false }

/-! ## 1. Teoremas de Seguridad contra Reentrancia y Conservación de Solvencia -/

/-- TEOREMA 1 (Inmunidad Total frente a Llamadas Reentrantes):
    Si el contrato está en medio de una interacción externa (`s.locked = true`),
    cualquier intento de llamada reentrante a `beginWithdrawCEI s reentrantAmount` es rechazado
    y deja el estado exactamente intacto (`= s`). -/
theorem reentrant_call_blocked (s : VaultState) (reentrantAmount : Nat)
    (hLocked : s.locked = true) :
    beginWithdrawCEI s reentrantAmount = s := by
  dsimp [beginWithdrawCEI]
  rw [hLocked]
  rfl

/-- TEOREMA 2 (Doble Retiro Reentrante Imposible):
    Aunque un contrato atacante intente llamar recursivamente a `beginWithdrawCEI` con `amount2`
    inmediatamente después de `beginWithdrawCEI s amount1` (antes de `endWithdrawCEI`),
    cuando el primer retiro tuvo éxito la segunda llamada no extrae ni un solo wei adicional! -/
theorem double_reentrant_withdraw_impossible (s : VaultState) (amount1 amount2 : Nat)
    (hNotLocked : s.locked = false)
    (hBal : amount1 ≤ s.userBal)
    (hVault : amount1 ≤ s.vault) :
    beginWithdrawCEI (beginWithdrawCEI s amount1) amount2 = beginWithdrawCEI s amount1 := by
  have h1 : (beginWithdrawCEI s amount1).locked = true := by
    dsimp [beginWithdrawCEI]
    rw [hNotLocked]
    simp [hBal, hVault]
  exact reentrant_call_blocked (beginWithdrawCEI s amount1) amount2 h1

/-- TEOREMA 3 (Conservación Exacta del Patrimonio del Usuario en CEI):
    Para cualquier estado `s` y cualquier cantidad solicitada `amount`,
    la suma `userBal + withdrawn` antes y después de `beginWithdrawCEI` es idéntica! -/
theorem cei_user_wealth_conservation (s : VaultState) (amount : Nat) :
    (beginWithdrawCEI s amount).userBal + (beginWithdrawCEI s amount).withdrawn =
      s.userBal + s.withdrawn := by
  dsimp [beginWithdrawCEI]
  split
  · rfl
  · split
    · next hOk =>
      dsimp
      omega
    · rfl

/-- TEOREMA 4 (Invariancia de Solvencia de la Bóveda):
    Si la bóveda es solvente (`s.userBal ≤ s.vault`), sigue siendo solvente tras `beginWithdrawCEI`. -/
theorem cei_preserves_solvency (s : VaultState) (amount : Nat)
    (hSolvent : IsSolvent s) :
    IsSolvent (beginWithdrawCEI s amount) := by
  dsimp [IsSolvent, beginWithdrawCEI] at hSolvent ⊢
  split
  · exact hSolvent
  · split
    · next hOk =>
      dsimp
      omega
    · exact hSolvent

end LeanTT.M58
