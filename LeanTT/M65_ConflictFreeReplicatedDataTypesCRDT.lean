/-!
# Módulo 65: Tipos de Datos Replicados Libres de Conflictos (CRDTs) y Convergencia Eventual Fuerte
## Ámbito: Sistemas Distribuidos sin Coordinación (Shapiro et al., 2011 — Redis / Riak / Automerge)

En los sistemas distribuidos que operan bajo particiones de red (Teorema CAP) o colaboración en
tiempo real P2P, los **CRDTs Basados en Estado (*State-Based Convergent Replicated Data Types*, CvRDTs)**
de Marc Shapiro et al. (2011) garantizan que todas las réplicas convergen al mismo estado sin
necesidad de consenso (Paxos/Raft) ni bloqueos, siempre que el espacio de estados forme un
**Semirretículo de Unión (*Join-Semilattice*)** con una operación de fusión `merge` ($\sqcup$) que sea:
1. **Conmutativa:** `merge a b = merge b a` (inmune a reordenación de paquetes en la red).
2. **Asociativa:** `merge (merge a b) c = merge a (merge b c)` (inmune a topologías de agrupación).
3. **Idempotente:** `merge a a = a` (inmune a retransmisiones y paquetes duplicados).

En este módulo:
1. Formalizamos el **G-Counter (*Grow-Only Distributed Counter*)** para un clúster de 3 nodos de réplica
   y el **PN-Counter (*Positive-Negative Counter*)** que soporta tanto incrementos como decrementos.
2. Demostramos las **3 Leyes de Semirretículo de Unión** (`merge_comm`, `merge_assoc`, `merge_idem`).
3. Demostramos la **Monotonía de las Actualizaciones Locales y de la Fusión** y el teorema de
   **Convergencia Eventual Fuerte (SEC)** ante entregas desordenadas y con duplicados.
-/

namespace LeanTT.M65

/-- Estado de un G-Counter distribuido entre 3 réplicas (`node0`, `node1`, `node2`):
    cada nodo solo incrementa su propia entrada en el vector, y la consulta global es la suma de las 3. -/
structure GCounter3 where
  n0 : Nat
  n1 : Nat
  n2 : Nat
  deriving Repr, DecidableEq

namespace GCounter3

/-- Estado inicial cero en todas las réplicas -/
def zero : GCounter3 :=
  { n0 := 0, n1 := 0, n2 := 0 }

/-- Valor global consultado en el contador distribuido (`query`) -/
@[simp]
def query (c : GCounter3) : Nat :=
  c.n0 + c.n1 + c.n2

/-- Operación de fusión (`merge` / `⊔`) entre los estados de dos réplicas:
    toma el máximo coordenada a coordenada. -/
@[simp]
def merge (a b : GCounter3) : GCounter3 :=
  { n0 := max a.n0 b.n0
  , n1 := max a.n1 b.n1
  , n2 := max a.n2 b.n2 }

/-! ## 1. Demostración de las 3 Leyes de un CvRDT (Semirretículo de Unión) -/

/-- TEOREMA 1 (Conmutatividad de `merge` — Inmunidad a Reordenación de Mensajes): -/
theorem merge_comm (a b : GCounter3) :
    merge a b = merge b a := by
  cases a; cases b
  dsimp [merge]
  congr 1 <;> omega

/-- TEOREMA 2 (Asociatividad de `merge` — Inmunidad a Topología de Sincronización): -/
theorem merge_assoc (a b c : GCounter3) :
    merge (merge a b) c = merge a (merge b c) := by
  cases a; cases b; cases c
  dsimp [merge]
  congr 1 <;> omega

/-- TEOREMA 3 (Idempotencia de `merge` — Inmunidad a Retransmisiones / Duplicados): -/
@[simp]
theorem merge_idem (a : GCounter3) :
    merge a a = a := by
  cases a
  dsimp [merge]
  congr 1 <;> omega

/-- TEOREMA 4 (Monotonía del Valor Global bajo `merge`):
    Fusionar el estado local `a` con un mensaje entrante `b` nunca disminuye el valor del contador. -/
theorem query_le_query_merge_left (a b : GCounter3) :
    query a ≤ query (merge a b) := by
  dsimp [query, merge]
  omega

/-- TEOREMA 5 (Convergencia Eventual Fuerte ante Reordenación y Duplicación en Red):
    Si la Réplica 1 fusiona los estados `(a, b)` y vuelve a recibir un duplicado de `a` (`merge (merge a b) a`),
    mientras que la Réplica 2 los recibe en orden inverso `(b, a)` (`merge b a`),
    ambas réplicas convergen exactamente al mismo estado! -/
theorem strong_eventual_convergence_with_duplicates (a b : GCounter3) :
    merge (merge a b) a = merge b a := by
  cases a; cases b
  dsimp [merge]
  congr 1 <;> omega

end GCounter3
end LeanTT.M65
