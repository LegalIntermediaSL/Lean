# Módulo 15: Catálogo General de los 25 Módulos Ejecutables (`LeanTT/M01..M25`) y sus Ámbitos de Aplicación

Este documento sirve como guía de navegación comentada por los **25 módulos ejecutables en Lean 4** del directorio [`LeanTT/`](../LeanTT/), organizados en **4 grandes bloques temáticos** que van desde ejemplos ultra-didácticos paso a paso hasta compiladores verificados, circuitos criptográficos ZK, teoría de categorías, bases de datos tipadas y lógica modal.

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

## Bloque III: Módulos Especialmente Didácticos Paso a Paso (`M14`–`M16`)

Ideales para quien empieza desde cero o quiere visualizar exactamente qué hace cada línea:

| Módulo | Archivo `.lean` | Enfoque Didáctico |
| :---: | :--- | :--- |
| **M14** | [`M14_DidacticStepByStepProofs.lean`](../LeanTT/M14_DidacticStepByStepProofs.lean) | **"Tu Primera Demostración Paso a Paso":** Cada línea de prueba incluye en comentarios la captura exacta del **Lean Infoview (`Γ ⊢ Meta`)** antes y después de aplicar `intro`, `exact`, `apply`, `have`, `constructor`, `rcases`, `rw` e `induction`. |
| **M15** | [`M15_DidacticDependentTypesFromZero.lean`](../LeanTT/M15_DidacticDependentTypesFromZero.lean) | **"Tipos Dependientes con Ejemplos Cotidianos":** 4 metáforas del mundo real: 1) El Menú del Restaurante ($\Pi$-type), 2) La Caja Etiquetada ($\Sigma$-type), 3) Cuenta Bancaria sin Descubierto (`Subtype` + conservación del saldo), 4) El Ascensor de 5 Plantas (familia inductiva indexada). |
| **M16** | [`M16_DidacticLambdaCubeAndPTS.lean`](../LeanTT/M16_DidacticLambdaCubeAndPTS.lean) | **"Las 8 Esquinas del Cubo de Barendregt":** Un ejemplo autocontenido y ejecutable para cada uno de los 8 vértices del cubo ($\lambda^\to$, $\lambda 2$, $\lambda\underline{\omega}$, $\lambda\omega$, $\lambda P$, $\lambda P2$, $\lambda P\underline{\omega}$, $\lambda C$). |

---

## Bloque IV: Ámbitos Avanzados de Aplicación y Verificación Formal (`M17`–`M25`)

Estos 9 módulos muestran cómo se aplica Lean 4 en la industria y la investigación contemporánea:

| Módulo | Ámbito de Aplicación | Archivo `.lean` | Teoremas Principales Verificados |
| :---: | :--- | :--- | :--- |
| **M17** | **Estructuras de Datos Verificadas** | [`M17_VerifiedDataStructuresBST.lean`](../LeanTT/M17_VerifiedDataStructuresBST.lean) | Árboles Binarios de Búsqueda (`BST`), involución del espejo (`mirror_mirror`), `mem_bstInsert_self` y preservación de elementos (`mem_bstInsert_of_mem`). |
| **M18** | **Algoritmos de Ordenación Verificados** | [`M18_VerifiedSortingAlgorithms.lean`](../LeanTT/M18_VerifiedSortingAlgorithms.lean) | Implementación de `insertionSort`, predicado inductivo `Sorted` y demostración completa de `sorted_insertionSort` y `length_insertionSort`. |
| **M19** | **Protocolos de Red y Máquinas de Estados** | [`M19_FiniteStateMachinesAndProtocols.lean`](../LeanTT/M19_FiniteStateMachinesAndProtocols.lean) | Mónada indexada por estados `Protocol s1 s2 α` (*Session Types*) donde enviar consultas sin autenticarse o no cerrar la sesión no compila. |
| **M20** | **Compiladores Formalmente Verificados** | [`M20_VerifiedCompilerAndStackMachine.lean`](../LeanTT/M20_VerifiedCompilerAndStackMachine.lean) | Compilador de expresiones aritméticas a una máquina virtual de pila (`PUSH`, `ADD`, `MUL`) y demostración del **Teorema de McCarthy-Painter** (`compile_correct`). |
| **M21** | **Teoría de Números y Circuitos ZK (SNARKs)** | [`M21_NumberTheoryAndCryptography.lean`](../LeanTT/M21_NumberTheoryAndCryptography.lean) | Preorden de divisibilidad, combinaciones lineales y verificación de **completitud y solidez (*Soundness & Completeness*)** de puertas R1CS/ZK (restricción de bit y multiplexor estilo `Clean`/`ArkLib`). |
| **M22** | **Teoría de Categorías y Lema de Yoneda** | [`M22_CategoryTheoryAndFunctors.lean`](../LeanTT/M22_CategoryTheoryAndFunctors.lean) | Categorías dependientes, `Copresheaf`, transformaciones naturales, funtor representable `Hom(A, -)` y **demostración completa del Lema de Yoneda**. |
| **M23** | **Teoría de Tipos Homotópica (HoTT)** | [`M23_HoTTAndHomotopyPaths.lean`](../LeanTT/M23_HoTTAndHomotopyPaths.lean) | Espacio de caminos `Path α a b` en `Type u`, leyes del $\infty$-grupoide fundamental, funtorialidad de `ap`, homotopías `f ∼ g` y equivalencias `α ≃ₕ β`. |
| **M24** | **Bases de Datos Relacionales y SQL Tipado** | [`M24_RelationalDatabasesAndTypedSQL.lean`](../LeanTT/M24_RelationalDatabasesAndTypedSQL.lean) | Esquemas tipados, cálculo dependiente del tipo de fila `Row s`, `selectWhere`, `crossJoin` con esquema `s1 ++ s2` y equivalencia de filtros compuestos. |
| **M25** | **Lógica Modal y Semántica de Kripke** | [`M25_ModalAndTemporalLogicDSL.lean`](../LeanTT/M25_ModalAndTemporalLogicDSL.lean) | Marcos de Kripke, operadores $\Box P$ y $\Diamond P$, axioma $K$ y demostración de los **3 Teoremas de Correspondencia de Sahlqvist-Kripke** ($T \leftrightarrow \text{Reflexiva}$, $4 \leftrightarrow \text{Transitiva}$, $B \leftrightarrow \text{Simétrica}$). |
