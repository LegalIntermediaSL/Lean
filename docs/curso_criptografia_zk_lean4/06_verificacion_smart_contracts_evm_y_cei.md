# Lección 06: Verificación Formal de Smart Contracts (EVM) y Mecanismos Económicos — Conservación, Patrón CEI y Subasta de Vickrey

> **Navegación del Mini-Curso:** [⬅️ Lección 05: Criptografía Post-Cuántica LWE](05_criptografia_postcuantica_reticulos_lwe.md) | [🏠 Índice del Mini-Curso ZK](00_indice_minicurso_zk_y_cripto.md)
>
> **Módulos ejecutables relacionados:** [`LeanTT/M30_SmartContractsAndEVMState.lean`](../../LeanTT/M30_SmartContractsAndEVMState.lean), [`LeanTT/M56_GameTheoryNashEquilibriumAndVCG.lean`](../../LeanTT/M56_GameTheoryNashEquilibriumAndVCG.lean) y [`LeanTT/M58_SmartContractReentrancyAndCEI.lean`](../../LeanTT/M58_SmartContractReentrancyAndCEI.lean).

---

## 1. Las Tres Propiedades Críticas de un Smart Contract Verificado en Lean 4

Cuando verificamos formalmente en Lean 4 un contrato inteligente (como un token ERC-20, una bóveda DeFi o un mecanismo de subasta on-chain), los tests unitarios para unos pocos valores concretos no bastan: buscamos **teoremas universales ($\forall$) sobre todas las transiciones posibles de estado**.

Las tres familias de invariantes más importantes son:

1. **Invariantes Contables de Conservación y Aislamiento ([`M30`](../../LeanTT/M30_SmartContractsAndEVMState.lean)):**
   * **Conservación bilateral de masa:** En cualquier transferencia `transfer s from to amount`, la suma de los balances del emisor y del receptor antes y después de la transacción es idéntica (no se crean ni se destruyen tokens por desbordamiento o error lógico).
   * **Aislamiento de cuentas de terceros (*Frame Property*):** Si `other ≠ from` y `other ≠ to`, el balance de `other` permanece estrictamente inalterado.
2. **Invariantes de Control de Flujo y Anti-Reentrancia ([`M58`](../../LeanTT/M58_SmartContractReentrancyAndCEI.lean)):**
   * En la EVM, enviar Ether o invocar un hook externo transfiere temporalmente el control de ejecución al contrato receptor.
   * Si el contrato receptor vuelve a llamar a `withdraw` antes de que hayamos descontado su saldo, vacía toda la bóveda (*The DAO Hack*, 2016).
3. **Invariantes de Compatibilidad de Incentivos / Teoría de Juegos ([`M56`](../../LeanTT/M56_GameTheoryNashEquilibriumAndVCG.lean)):**
   * Incluso si el código no tiene bugs técnicos, ¿puede un participante manipular el protocolo mintiendo sobre su valoración privada?

---

## 2. Anatomía Formal de un Ataque de Reentrancia vs. el Patrón CEI

Comparemos mediante un diagrama de secuencia por qué un contrato que actualiza el estado *después* de la interacción externa es vulnerable y cómo el patrón **Checks-Effects-Interactions (CEI) + `ReentrancyGuard`** lo bloquea matemáticamente:

```mermaid
sequenceDiagram
    participant A as Contrato Atacante
    participant V as Bóveda Protegida (Patrón CEI + locked)
    A->>V: 1. Llama a beginWithdrawCEI(amount1)
    Note over V: CHECK: !locked && amount1 ≤ userBal ≤ vault<br/>EFFECT: userBal -= amount1; vault -= amount1; locked := true
    V->>A: 2. Interacción externa (envío de fondos)
    A->>V: 3. Ataque Reentrante: Llama de nuevo a beginWithdrawCEI(amount2)
    Note over V: CHECK FALLA: locked == true!<br/>Devuelve el estado intacto (0 wei extraídos)
    V-->>A: 4. Termina interacción y ejecuta endWithdrawCEI (locked := false)
```

En el módulo [`LeanTT/M58_SmartContractReentrancyAndCEI.lean`](../../LeanTT/M58_SmartContractReentrancyAndCEI.lean) están demostrados los cuatro teoremas que certifican este diseño:
1. **`reentrant_call_blocked`:** Toda llamada con `s.locked = true` es una operación nula (`= s`).
2. **`double_reentrant_withdraw_impossible`:** Llamar dos veces seguidas a `beginWithdrawCEI` sin haber cerrado el ciclo con `endWithdrawCEI` jamás extrae fondos en la segunda llamada.
3. **`cei_user_wealth_conservation`:** La suma `userBal + withdrawn` es invariante en todo paso.
4. **`cei_preserves_solvency`:** Si `userBal ≤ vault` antes del retiro, sigue cumpliéndose `userBal ≤ vault` después del retiro.

---

## 3. Seguridad Económica On-Chain: El Teorema de Vickrey (DSIC) en Lean 4

En las subastas de gobernanza, liquidaciones DeFi o asignación de espacio en bloques, queremos mecanismos donde **ningún participante gane nada mintiendo u ocultando su valoración real** (*Dominant-Strategy Incentive Compatibility*, **DSIC**).

En [`LeanTT/M56_GameTheoryNashEquilibriumAndVCG.lean`](../../LeanTT/M56_GameTheoryNashEquilibriumAndVCG.lean) formalizamos la **Subasta de Segundo Precio de Vickrey** y demostramos en cuatro líneas gracias a `split` y `omega` que decir la verdad (`b1 = v1`) domina a cualquier estrategia alternativa `b1'`:

```lean
import LeanTT.M56_GameTheoryNashEquilibriumAndVCG
import LeanTT.M58_SmartContractReentrancyAndCEI

namespace CursoZK.Leccion06

open LeanTT.M56
open LeanTT.M58

/-- TEOREMA INTEGRADO (Solvencia de Ciclo Completo de Retiro CEI + Liberación de Cerrojo):
    Si una bóveda comienza solvente (`IsSolvent s`), ejecutar un retiro completo con el patrón CEI
    seguido de la liberación del cerrojo (`endWithdrawCEI (beginWithdrawCEI s amount)`)
    deja el cerrojo desbloqueado (`locked = false`) y preserva la solvencia de la bóveda! -/
theorem full_withdraw_cycle_solvent_and_unlocked (s : VaultState) (amount : Nat)
    (hSolvent : IsSolvent s) :
    let sFinal := endWithdrawCEI (beginWithdrawCEI s amount)
    sFinal.locked = false ∧ IsSolvent sFinal := by
  refine ⟨rfl, ?_⟩
  have h1 : IsSolvent (beginWithdrawCEI s amount) :=
    cei_preserves_solvency s amount hSolvent
  exact h1

end CursoZK.Leccion06
```

---

## 4. Ejercicio Práctico de la Lección 06

### Ejercicio 6.1: Idempotencia de Intentar Retirar Más que el Saldo Disponible
Demuestra en Lean 4 que si un usuario intenta retirar una cantidad `amount > s.userBal` en `beginWithdrawCEI s amount`, la transacción no altera el estado de la bóveda (`beginWithdrawCEI s amount = s`).

<details>
<summary>💡 <b>Ver Solución Comentada en Lean 4</b></summary>

```lean
import LeanTT.M58_SmartContractReentrancyAndCEI

open LeanTT.M58

theorem withdraw_over_balance_is_noop (s : VaultState) (amount : Nat)
    (hOver : s.userBal < amount) :
    beginWithdrawCEI s amount = s := by
  dsimp [beginWithdrawCEI]
  split
  · rfl
  · split
    · next hOk => omega
    · rfl
```
</details>

---

⬅️ [**Volver al Índice del Mini-Curso de Criptografía ZK, Post-Cuántica y Smart Contracts (`00_indice_minicurso_zk_y_cripto.md`)**](00_indice_minicurso_zk_y_cripto.md)
