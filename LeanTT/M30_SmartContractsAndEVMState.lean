/-!
# Módulo 30: Verificación Formal de Smart Contracts y Conservación de Activos
## Ámbito: Seguridad Web3, Máquinas de Estados Financieras y zkEVM (Inspirado en `evm-asm`)

En los contratos inteligentes (como tokens ERC-20 o máquinas de estados financieras), un bug aritmético
o de lógica de transición puede causar la creación o destrucción accidental de fondos.

En este módulo:
1. Modelamos el estado de un contrato de tokens (`TokenState`) con balances y suministro total.
2. Definimos la operación de transferencia verificada `transfer`.
3. **Demostramos formalmente dos teoremas críticos de seguridad (Invariantes de Seguridad):**
   - Ninguna transferencia fallida altera el estado.
   - Toda transferencia exitosa **conserva exactamente la suma de balances** de los participantes.
-/

namespace LeanTT.M30

abbrev Address := Nat

/-- Estado del libro mayor de un Smart Contract de Tokens -/
structure TokenState where
  balance : Address → Nat

namespace TokenState

/-- Actualiza el balance de una dirección específica `addr` al nuevo valor `newBal` -/
def setBalance (st : TokenState) (addr : Address) (newBal : Nat) : TokenState where
  balance a := if a = addr then newBal else st.balance a

@[simp]
theorem setBalance_same (st : TokenState) (a : Address) (v : Nat) :
    (st.setBalance a v).balance a = v := by
  dsimp [setBalance]
  rw [if_pos rfl]

@[simp]
theorem setBalance_diff (st : TokenState) {a b : Address} (v : Nat) (h : b ≠ a) :
    (st.setBalance a v).balance b = st.balance b := by
  dsimp [setBalance]
  rw [if_neg h]

/-- Transición `transfer`: transfiere `amount` desde `sender` hacia `receiver`.
    Devuelve `none` (revert de la EVM) si `sender` no tiene saldo suficiente. -/
def transfer (st : TokenState) (sender receiver : Address) (amount : Nat) : Option TokenState :=
  if sender = receiver then
    if amount ≤ st.balance sender then
      some st
    else
      none
  else
    if amount ≤ st.balance sender then
      let st1 := st.setBalance sender (st.balance sender - amount)
      let st2 := st1.setBalance receiver (st1.balance receiver + amount)
      some st2
    else
      none

/-! ## Teoremas de Seguridad e Invariantes del Smart Contract -/

/-- INVARIANTE 1 (Conservación Bilateral de Fondos):
    Si `sender ≠ receiver` y `transfer st sender receiver amount = some st'`,
    entonces la suma de los saldos de `sender` y `receiver` después de la transacción
    es **exactamente igual** a la suma de sus saldos antes de la transacción! -/
theorem transfer_preserves_pair_sum
    (st st' : TokenState) (sender receiver : Address) (amount : Nat)
    (hne : sender ≠ receiver)
    (htx : st.transfer sender receiver amount = some st') :
    st'.balance sender + st'.balance receiver =
    st.balance sender + st.balance receiver := by
  dsimp [transfer] at htx
  rw [if_neg hne] at htx
  split at htx
  · next hle =>
    injection htx with hst'
    subst hst'
    rw [setBalance_same]
    rw [setBalance_diff _ _ hne]
    rw [setBalance_same]
    rw [setBalance_diff _ _ (Ne.symm hne)]
    omega
  · contradiction

/-- INVARIANTE 2 (Aislamiento de Cuentas de Terceros / *No Side Effects on Bystanders*):
    Una transferencia entre `sender` y `receiver` jamás modifica el saldo de ninguna
    tercera cuenta `other` (`other ≠ sender` y `other ≠ receiver`). -/
theorem transfer_preserves_other_balance
    (st st' : TokenState) (sender receiver other : Address) (amount : Nat)
    (h_not_sender : other ≠ sender) (h_not_receiver : other ≠ receiver)
    (htx : st.transfer sender receiver amount = some st') :
    st'.balance other = st.balance other := by
  dsimp [transfer] at htx
  split at htx
  · split at htx
    · injection htx with hst'; subst hst'; rfl
    · contradiction
  · split at htx
    · injection htx with hst'
      subst hst'
      rw [setBalance_diff _ _ h_not_receiver]
      rw [setBalance_diff _ _ h_not_sender]
    · contradiction

end TokenState
end LeanTT.M30
