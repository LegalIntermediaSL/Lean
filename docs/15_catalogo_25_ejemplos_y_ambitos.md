# Módulo 15: Catálogo General de los 40 Módulos Ejecutables (`LeanTT/M01..M40`) y Talleres de Ejercicios

Este documento es el mapa maestro de los **40 módulos ejecutables en Lean 4** del directorio [`LeanTT/`](../LeanTT/) y los talleres de ejercicios en [`LeanTT/Exercises/`](../LeanTT/Exercises/).

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

## Bloque III: Módulos Especialmente Didácticos Paso a Paso (`M14`–`M16`) y Talleres (`E01`/`S01`)

| Módulo | Archivo `.lean` | Enfoque Didáctico |
| :---: | :--- | :--- |
| **M14** | [`M14_DidacticStepByStepProofs.lean`](../LeanTT/M14_DidacticStepByStepProofs.lean) | **"Tu Primera Demostración Paso a Paso":** Cada línea de prueba incluye en comentarios la captura exacta del **Lean Infoview (`Γ ⊢ Meta`)** antes y después de cada táctica. |
| **M15** | [`M15_DidacticDependentTypesFromZero.lean`](../LeanTT/M15_DidacticDependentTypesFromZero.lean) | **"Tipos Dependientes con Ejemplos Cotidianos":** Menú del Restaurante ($\Pi$-type), Caja Etiquetada ($\Sigma$-type), Cuenta Bancaria sin Descubierto y Ascensor de 5 Plantas. |
| **M16** | [`M16_DidacticLambdaCubeAndPTS.lean`](../LeanTT/M16_DidacticLambdaCubeAndPTS.lean) | **"Las 8 Esquinas del Cubo de Barendregt":** Un ejemplo ejecutable para cada uno de los 8 vértices del cubo ($\lambda^\to$ a $\lambda C$). |
| **E01 / S01** | [`Exercises/E01_WorkoutLambdaAndLogic.lean`](../LeanTT/Exercises/E01_WorkoutLambdaAndLogic.lean) | Taller interactivo de ejercicios con pistas progresivas y solucionario comparado en [`Solutions/S01_WorkoutLambdaAndLogic.lean`](../LeanTT/Solutions/S01_WorkoutLambdaAndLogic.lean). |

---

## Bloque IV: 24 Ámbitos Avanzados de Aplicación y Verificación Formal (`M17`–`M40`)

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
| **M40** | **Mini-Kernel de Tipos Dependientes** | [`M40_MiniDependentTypeChecker.lean`](../LeanTT/M40_MiniDependentTypeChecker.lean) | **Proyecto Cumbre:** Implementación en Lean 4 de un verificador de tipos dependientes con universos, $\Pi$-types, `whnf` y sustitución de De Bruijn. |
