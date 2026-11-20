# Módulo 15: Catálogo General de los 60 Módulos Ejecutables (`LeanTT/M01..M60`) y 4 Talleres de Ejercicios

Este documento es el mapa maestro de los **60 módulos ejecutables en Lean 4** del directorio [`LeanTT/`](../LeanTT/) y los **4 talleres de ejercicios con solucionarios comentados** en [`LeanTT/Exercises/`](../LeanTT/Exercises/) y [`LeanTT/Solutions/`](../LeanTT/Solutions/).

---

## Bloque I: Núcleo Teórico — Cálculo Lambda, Tipos Dependientes y Lógica (`M01`–`M07`, `M13`)

| Módulo | Archivo `.lean` | Qué Aprenderás y Demostrarás |
| :---: | :--- | :--- |
| **M01** | [`M01_LambdaCalculus.lean`](../LeanTT/M01_LambdaCalculus.lean) | Currificación, las 6 reducciones del kernel ($\beta, \eta, \delta, \iota, \zeta$, proyecciones), combinadores $S, K, I, B, C$, booleanos y numerales de Church en el Sistema $F$. |
| **M02** | [`M02_DependentTypes.lean`](../LeanTT/M02_DependentTypes.lean) | Tipos $\Pi$ (`(x : A) → B x`), Tipos $\Sigma$ (`(x : A) × B x`), distributividad $\Pi/\Sigma$, subtipos `{x : α // P x}` y un **`printf` estáticamente tipado**. |
| **M03** | [`M03_UniversesAndProp.lean`](../LeanTT/M03_UniversesAndProp.lean) | Jerarquía `Sort u` (`Prop : Type 0 : Type 1`), polimorfismo de universos, `ULift`, impredicatividad de `Prop`, irrelevancia de prueba y eliminación de *subsingletons*. |
| **M04** | [`M04_CurryHoward.lean`](../LeanTT/M04_CurryHoward.lean) | Isomorfismo de Curry-Howard con términos $\lambda$ puros, leyes de De Morgan constructivas vs clásicas, teorema de Glivenko (`¬¬(P ∨ ¬P)`) y Ley de Peirce. |
| **M05** | [`M05_InductiveFamilies.lean`](../LeanTT/M05_InductiveFamilies.lean) | Predicado inductivo `EsPar`, ordinales finitos `Fin' n`, vectores `Vec α n` con indexación segura `get`, eliminadores `Nat.rec` y recursión bien fundada. |
| **M06** | [`M06_EqualityAndTransport.lean`](../LeanTT/M06_EqualityAndTransport.lean) | El tipo identidad `Eq`, derivación de simetría, transitividad y congruencia desde `Eq.rec`, `funext`, `propext` y construcción de $\mathbb{Z}$ como cociente de $\mathbb{N} \times \mathbb{N}$. |
| **M07** | [`M07_TypeClassesAndAlgebra.lean`](../LeanTT/M07_TypeClassesAndAlgebra.lean) | Jerarquía algebraica (`Semigrupo` $\to$ `Monoide` $\to$ `Grupo`), unicidad del neutro, $(a^{-1})^{-1} = a$, $(a \star b)^{-1} = b^{-1} \star a^{-1}$, grupo producto y coerción `CoeFun`. |
| **M13** | [`M13_FoundationsOfDependentTypeTheory.lean`](../LeanTT/M13_FoundationsOfDependentTypeTheory.lean) | Las 5 reglas canónicas de Martin-Löf, *Large Elimination*, `VectorRecursivo`, eliminador $J$, contractibilidad del espacio basado `(y : A) × (a = y)` y codificación de `Nat` mediante **$W$-Types**. |

---

## Bloque II: Tácticas, Efectos Monádicos, Metateoría y Metaprogramación (`M08`–`M12`)

| Módulo | Archivo `.lean` | Qué Aprenderás y Demostrarás |
| :---: | :--- | :--- |
| **M08** | [`M08_TacticsAndCalculationalProofs.lean`](../LeanTT/M08_TacticsAndCalculationalProofs.lean) | Comparación término $\lambda$ vs bloque `by`, demostración de la fórmula de Gauss ($2\sum_{i=0}^n i = n(n+1)$) con `calc`, modo `conv`, `simp`, `decide` y `omega`. |
| **M09** | [`M09_MonadsAndEffects.lean`](../LeanTT/M09_MonadsAndEffects.lean) | Creación de la mónada `WriterNat`, demostración de su instancia `LawfulMonad`, conteo verificado de pasos de Collatz y evaluador con `ExceptT` + `StateM`. |
| **M10** | [`M10_MetatheorySTLC.lean`](../LeanTT/M10_MetatheorySTLC.lean) | Formalización intrínsecamente tipada del Cálculo $\lambda$ Simplemente Tipado (STLC) con índices de De Bruijn (`Var Γ τ`, `Term Γ τ`), renombramiento, sustitución paralela y evaluador denotacional. |
| **M11** | [`M11_OperationalSemantics.lean`](../LeanTT/M11_OperationalSemantics.lean) | Semántica operacional de Paso Grande (`e ⇓ n`) y Paso Pequeño (`e ⟶ e'`), clausura reflexiva-transitiva (`e ⟶* e'`), determinismo y teorema de equivalencia. |
| **M12** | [`M12_MetaprogrammingAndTactics.lean`](../LeanTT/M12_MetaprogrammingAndTactics.lean) | Construcción manual de ASTs del kernel (`Lean.Expr`), inferencia en `MetaM`, macros higiénicas, mini-DSL de conjuntos y creación de la táctica `buscar_hipotesis` en `TacticM`. |

---

## Bloque III: Módulos Especialmente Didácticos (`M14`–`M16`) y 4 Talleres Prácticos (`E01`–`E04`)

| Módulo | Archivo `.lean` | Enfoque Didáctico |
| :---: | :--- | :--- |
| **M14** | [`M14_DidacticStepByStepProofs.lean`](../LeanTT/M14_DidacticStepByStepProofs.lean) | **"Tu Primera Demostración Paso a Paso":** Cada línea de prueba incluye en comentarios la captura exacta del **Lean Infoview (`Γ ⊢ Meta`)** antes y después de cada táctica. |
| **M15** | [`M15_DidacticDependentTypesFromZero.lean`](../LeanTT/M15_DidacticDependentTypesFromZero.lean) | **"Tipos Dependientes con Ejemplos Cotidianos":** Menú del Restaurante ($\Pi$-type), Caja Etiquetada ($\Sigma$-type), Cuenta Bancaria sin Descubierto y Ascensor de 5 Plantas. |
| **M16** | [`M16_DidacticLambdaCubeAndPTS.lean`](../LeanTT/M16_DidacticLambdaCubeAndPTS.lean) | **"Las 8 Esquinas del Cubo de Barendregt":** Un ejemplo ejecutable para cada uno de los 8 vértices del cubo ($\lambda^\to$ a $\lambda C$). |
| **E01 / S01** | [`Exercises/E01_WorkoutLambdaAndLogic.lean`](../LeanTT/Exercises/E01_WorkoutLambdaAndLogic.lean) | **Taller 01 (Cálculo $\lambda$ y Lógica):** Combinador `flip`, involución por $\beta$-reducción, disyunción y subtipos ([Solucionario `S01`](../LeanTT/Solutions/S01_WorkoutLambdaAndLogic.lean)). |
| **E02 / S02** | [`Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean`](../LeanTT/Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean) | **Taller 02 (Familias Inductivas y Vectores):** `head`/`tail` seguros, reconstrucción $\eta$ y leyes funtoriales de `VecE α n` ([Solucionario `S02`](../LeanTT/Solutions/S02_WorkoutInductiveFamiliesAndEquality.lean)). |
| **E03 / S03** | [`Exercises/E03_WorkoutVerificationAndCryptography.lean`](../LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean) | **Taller 03 (Circuitos ZK, Polinomios y Protocolos $\Sigma$):** Puertas R1CS (`NOT`, `AND`, `OR`, `XOR`), esquema de Horner y desafío cero en Schnorr ([Solucionario `S03`](../LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean)). |
| **E04 / S04** | [`Exercises/E04_WorkoutCompilersSTARKsAndGames.lean`](../LeanTT/Exercises/E04_WorkoutCompilersSTARKsAndGames.lean) | **Taller 04 (CPS, LTL, STARKs/FRI, Vickrey y `wp`):** Continuaciones CPS, distributividad e idempotencia temporal en LTL, diferencia simétrica en FRI y `wp` de Dijkstra ([Solucionario `S04`](../LeanTT/Solutions/S04_WorkoutCompilersSTARKsAndGames.lean)). |

---

## Bloque IV: 44 Ámbitos Avanzados de Aplicación y Verificación Formal (`M17`–`M60`)

| Módulo | Ámbito de Aplicación | Archivo `.lean` | Teoremas Principales Verificados |
| :---: | :--- | :--- | :--- |
| **M17** | **Estructuras de Datos Verificadas** | [`M17_VerifiedDataStructuresBST.lean`](../LeanTT/M17_VerifiedDataStructuresBST.lean) | Árboles Binarios de Búsqueda (`BST`), `mirror_mirror`, `mem_bstInsert_self` y `mem_bstInsert_of_mem`. |
| **M18** | **Algoritmos de Ordenación Verificados** | [`M18_VerifiedSortingAlgorithms.lean`](../LeanTT/M18_VerifiedSortingAlgorithms.lean) | Implementación de `insertionSort`, predicado inductivo `Sorted` y demostración de `sorted_insertionSort`. |
| **M19** | **Protocolos de Red y Tipos Sesión** | [`M19_FiniteStateMachinesAndProtocols.lean`](../LeanTT/M19_FiniteStateMachinesAndProtocols.lean) | Mónada indexada por estados `Protocol s1 s2 α` (*Session Types*) con auditoría de trazas. |
| **M20** | **Compiladores Verificados** | [`M20_VerifiedCompilerAndStackMachine.lean`](../LeanTT/M20_VerifiedCompilerAndStackMachine.lean) | Compilador a máquina de pila y demostración del **Teorema de McCarthy-Painter** (`compile_correct`). |
| **M21** | **Teoría de Números y Circuitos ZK** | [`M21_NumberTheoryAndCryptography.lean`](../LeanTT/M21_NumberTheoryAndCryptography.lean) | Preorden de divisibilidad y verificación de **Soundness & Completeness** de puertas R1CS/ZK (`BitConstraint`, `MuxConstraint`). |
| **M22** | **Teoría de Categorías y Yoneda** | [`M22_CategoryTheoryAndFunctors.lean`](../LeanTT/M22_CategoryTheoryAndFunctors.lean) | Categorías dependientes, `Copresheaf`, transformaciones naturales y **demostración completa del Lema de Yoneda**. |
| **M23** | **Teoría de Tipos Homotópica (HoTT)** | [`M23_HoTTAndHomotopyPaths.lean`](../LeanTT/M23_HoTTAndHomotopyPaths.lean) | Espacio de caminos `Path α a b` en `Type u`, leyes del $\infty$-grupoide, `ap`, homotopías `f ∼ g` y equivalencias `α ≃ₕ β`. |
| **M24** | **Bases de Datos y SQL Tipado** | [`M24_RelationalDatabasesAndTypedSQL.lean`](../LeanTT/M24_RelationalDatabasesAndTypedSQL.lean) | Esquemas tipados, cálculo dependiente del tipo de fila `Row s`, `selectWhere` y `crossJoin`. |
| **M25** | **Lógica Modal y Kripke** | [`M25_ModalAndTemporalLogicDSL.lean`](../LeanTT/M25_ModalAndTemporalLogicDSL.lean) | Marcos de Kripke, $\Box P$, $\Diamond P$, axioma $K$ y los **3 Teoremas de Correspondencia de Sahlqvist-Kripke** ($T, 4, B$). |
| **M26** | **Sistema F y Parametricidad** | [`M26_SystemFAndParametricity.lean`](../LeanTT/M26_SystemFAndParametricity.lean) | Paquetes existenciales impredicativos (ADTs) y naturalidad paramétrica de Reynolds (*Theorems for Free*). |
| **M27** | **Normalización por Evaluación (NbE)** | [`M27_NormalizationByEvaluation.lean`](../LeanTT/M27_NormalizationByEvaluation.lean) | Términos neutros `Ne`, formas normales $\beta\eta$ `Nf`, `reflect`, `reify` y normalizador completo `norm`. |
| **M28** | **Lógica Lineal y Borrow Checker** | [`M28_SubstructuralAndLinearTypes.lean`](../LeanTT/M28_SubstructuralAndLinearTypes.lean) | Cálculo $\lambda$ lineal con ranuras `free`/`used` donde duplicar u olvidar un recurso lineal no compila. |
| **M29** | **Lógica de Separación (`iris-lean`)** | [`M29_SeparationLogicAndHeap.lean`](../LeanTT/M29_SeparationLogicAndHeap.lean) | Heaps disjuntos, conjunción separadora `P ∗ Q`, `a ↦ₕ v`, monotonía del marco y exclusión mutua de punteros. |
| **M30** | **Smart Contracts y EVM (`evm-asm`)** | [`M30_SmartContractsAndEVMState.lean`](../LeanTT/M30_SmartContractsAndEVMState.lean) | Libro mayor de tokens y demostración de **conservación bilateral de fondos** y aislamiento de cuentas de terceros. |
| **M31** | **Protocolo Sum-Check (`ArkLib`)** | [`M31_SumCheckProtocolAndOracles.lean`](../LeanTT/M31_SumCheckProtocolAndOracles.lean) | Polinomios sobre el hipercubo booleano $\{0,1\}^2$ y demostración de **Completitud Perfecta** del protocolo Sum-Check. |
| **M32** | **Polinomios Computables (`CompPoly`)** | [`M32_ComputablePolynomialsAndFields.lean`](../LeanTT/M32_ComputablePolynomialsAndFields.lean) | Evaluación por el Esquema de Horner, `addPoly`, `scalePoly` y demostración de que la evaluación es un homomorfismo lineal. |
| **M33** | **Expresiones Regulares y Brzozowski** | [`M33_AutomataAndBrzozowskiDerivatives.lean`](../LeanTT/M33_AutomataAndBrzozowskiDerivatives.lean) | `Regex α`, anulabilidad `nullable`, derivadas de Brzozowski `deriv` y teoremas algebraicos de `accepts`. |
| **M34** | **Combinadores de Parsing Verificados** | [`M34_VerifiedParserCombinators.lean`](../LeanTT/M34_VerifiedParserCombinators.lean) | Leyes de monoide de la alternativa `<\|>ₚ` y demostración de progreso léxico estricto (`satisfy_decreases_length`). |
| **M35** | **Optimizador de Consultas SQL** | [`M35_SQLQueryOptimizerCorrectness.lean`](../LeanTT/M35_SQLQueryOptimizerCorrectness.lean) | Fusión de filtros y *Filter Pushdown* sobre `UNION` con demostración de equivalencia (`evalPlan_optimizePlan`). |
| **M36** | **Conexiones de Galois (`α ⊣ γ`)** | [`M36_GaloisConnectionsAndLattices.lean`](../LeanTT/M36_GaloisConnectionsAndLattices.lean) | Posets, adjunciones de Galois, unidad/counidad, monotonía e identidad triangular $\alpha \circ \gamma \circ \alpha = \alpha$. |
| **M37** | **Flujos Infinitos (`Stream`)** | [`M37_StreamsAndBisimulation.lean`](../LeanTT/M37_StreamsAndBisimulation.lean) | Observaciones coinductivas `head`/`tail`, desplegado `cons_head_tail` y conmutatividad de `tail` con `map`. |
| **M38** | **Diferenciación Automática (`SciLean`)** | [`M38_VerifiedAutomaticDifferentiation.lean`](../LeanTT/M38_VerifiedAutomaticDifferentiation.lean) | Números Duales $a + b\varepsilon$ ($\varepsilon^2 = 0$), regla de Leibniz y teorema de corrección de *Forward-Mode AD* frente a derivación simbólica. |
| **M39** | **Pruebas por Reflexión (`Reflection`)** | [`M39_ProofByReflectionAndBitVectors.lean`](../LeanTT/M39_ProofByReflectionAndBitVectors.lean) | Reificación sintáctica, normalizador de monoides `flatten` y cierre de identidades complejas mediante `rfl`. |
| **M40** | **Mini-Kernel de Tipos Dependientes** | [`M40_MiniDependentTypeChecker.lean`](../LeanTT/M40_MiniDependentTypeChecker.lean) | **Proyecto Cumbre I:** Implementación en Lean 4 de un verificador de tipos dependientes con universos, $\Pi$-types, `whnf` y sustitución de De Bruijn. |
| **M41** | **Flujo de Información y No-Interferencia** | [`M41_InformationFlowAndNonInterference.lean`](../LeanTT/M41_InformationFlowAndNonInterference.lean) | Retículo de confidencialidad `pub ⊑ₛ sec`, `LowEquiv` y demostración del **Teorema de No-Interferencia** (`non_interference`). |
| **M42** | **Protocolos $\Sigma$ (Schnorr) y HVZK** | [`M42_FiatShamirAndSigmaProtocols.lean`](../LeanTT/M42_FiatShamirAndSigmaProtocols.lean) | **Completitud**, **2-Special Soundness** (extracción de testigo) y **Simulador Zero-Knowledge (HVZK)** sin conocer el secreto $w$. |
| **M43** | **Motor de Políticas AWS Cedar** | [`M43_AuthorizationPolicyEngineCedar.lean`](../LeanTT/M43_AuthorizationPolicyEngineCedar.lean) | Inspirado en `cedar-spec`: demostración de `default_deny`, `forbid_overrides_permit` y `global_freeze_denies_all`. |
| **M44** | **Árboles de Merkle Indexados** | [`M44_MerkleTreesAndCryptographicCommitments.lean`](../LeanTT/M44_MerkleTreesAndCryptographicCommitments.lean) | `MerkleTree h`, `MerkleProof h`, **Completitud de inclusión** y reducción de **Binding** a colisiones explícitas de la función hash. |
| **M45** | **Tipos de Refinamiento (Liquid Types)** | [`M45_RefinementTypesAndLiquidPredicates.lean`](../LeanTT/M45_RefinementTypesAndLiquidPredicates.lean) | `PosNat`, intervalos acotados `Interval lo hi`, `clamp` verificado y cálculo intrínseco del punto medio `midpoint`. |
| **M46** | **Mónadas Libres y Efectos Algebraicos** | [`M46_FreeMonadsAndAlgebraicEffects.lean`](../LeanTT/M46_FreeMonadsAndAlgebraicEffects.lean) | Árbol de efectos `KVProg α`, las 3 leyes de mónada, manejador `handleState` y teorema *Read-After-Write*. |
| **M47** | **Consenso Distribuido y Quórums** | [`M47_DistributedConsensusAndQuorums.lean`](../LeanTT/M47_DistributedConsensusAndQuorums.lean) | Axioma de Intersección de Quórums y demostración formal de **Seguridad de Consenso (`quorum_agreement` / `chosen_unique`)**. |
| **M48** | **Árboles Rojo-Negro de Okasaki** | [`M48_CertifiedRedBlackTreeInvariants.lean`](../LeanTT/M48_CertifiedRedBlackTreeInvariants.lean) | Las 4 rotaciones de `balance` de Okasaki y demostración de preservación exacta de elementos (`mem_balance`, `mem_insert`). |
| **M49** | **Distribuciones y Cadenas de Markov** | [`M49_ProbabilityDistributionsAndMarkovChains.lean`](../LeanTT/M49_ProbabilityDistributionsAndMarkovChains.lean) | Inspirado en `VCV-io`: distribuciones discretas `Dist α` y conservación de masa total bajo `map`, `scale` y pasos de Markov (`bind`). |
| **M50** | **Elaborador Bidireccional (`synth`/`check`)** | [`M50_BidirectionalElaboratorAndUnification.lean`](../LeanTT/M50_BidirectionalElaboratorAndUnification.lean) | **Proyecto Cumbre II:** Sustituciones de metavariables `?m_i`, leyes de composición y elaborador bidireccional que infiere tipos omitidos en lambdas. |
| **M51** | **Transformación CPS y Teorema de Plotkin** | [`M51_ContinuationPassingStyleCPS.lean`](../LeanTT/M51_ContinuationPassingStyleCPS.lean) | Evaluador directo vs. estilo de paso de continuaciones `evalCPS e k` y demostración de `evalCPS e k = k (evalDirect e)`. |
| **M52** | **Forma SSA y Plegado de Constantes** | [`M52_StaticSingleAssignmentAndRegisterAlloc.lean`](../LeanTT/M52_StaticSingleAssignmentAndRegisterAlloc.lean) | Instrucciones SSA sobre banco de registros y demostración de preservación semántica de `foldProg` (`execProg_foldProg`). |
| **M53** | **Lógica Temporal Lineal (LTL)** | [`M53_LinearTemporalLogicModelChecking.lean`](../LeanTT/M53_LinearTemporalLogicModelChecking.lean) | Operadores temporales `next` ($\bigcirc$), `always` ($\Box$), `eventually` ($\Diamond$), `untilLTL` ($\mathcal{U}$), desplegado en punto fijo e inducción de invariantes. |
| **M54** | **Tipos de Sesión Binarios y Dualidad** | [`M54_ConcurrentProcessCalculusAndSessionDuality.lean`](../LeanTT/M54_ConcurrentProcessCalculusAndSessionDuality.lean) | Tipos de sesión de Honda, involutividad `dual (dual s) = s` y progreso libre de *deadlocks* en sincronización de canales. |
| **M55** | **zk-STARKs y Plegado Polinómico FRI** | [`M55_STARKsAndFRILowDegreeFolding.lean`](../LeanTT/M55_STARKsAndFRILowDegreeFolding.lean) | Descomposición par-impar $P(x) = P_{\text{even}}(x^2) + P_{\text{odd}}(x^2)\cdot x$, operador `friFold` y suma simétrica sobre $\{x, -x\}$. |
| **M56** | **Teoría de Juegos y Subasta de Vickrey** | [`M56_GameTheoryNashEquilibriumAndVCG.lean`](../LeanTT/M56_GameTheoryNashEquilibriumAndVCG.lean) | Demostración formal del **Teorema de Vickrey (DSIC)** (`vickrey_truthful_dominant`) y dominancia estricta en el Dilema del Prisionero. |
| **M57** | **Privacidad Diferencial y Sensibilidad $L_1$** | [`M57_DifferentialPrivacyAndSensitivity.lean`](../LeanTT/M57_DifferentialPrivacyAndSensitivity.lean) | Sensibilidad global `HasSensitivity`, subaditividad de consultas y comparación entre composición paralela ($\max$) y secuencial ($+$). |
| **M58** | **Reentrancia EVM y Patrón CEI** | [`M58_SmartContractReentrancyAndCEI.lean`](../LeanTT/M58_SmartContractReentrancyAndCEI.lean) | Protección *Checks-Effects-Interactions* + `ReentrancyGuard`: bloqueo de llamadas reentrantes, conservación de patrimonio y solvencia. |
| **M59** | **Lógica de Hoare y Dijkstra `wp`** | [`M59_SymbolicExecutionAndWP.lean`](../LeanTT/M59_SymbolicExecutionAndWP.lean) | Transformador de precondición más débil `wp c Q`, teorema `hoareTriple_iff_imp_wp` y verificación de intercambio aritmético *in-place*. |
| **M60** | **Kernel Polimórfico con `Sort u` y *Large Elimination*** | [`M60_UniversePolymorphicKernelAndInductives.lean`](../LeanTT/M60_UniversePolymorphicKernelAndInductives.lean) | **Proyecto Cumbre III:** Jerarquía `Sort u`, función `imaxLevel` para impredicatividad de `Prop` y eliminador dependiente `boolRec` en el kernel. |
