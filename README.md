# Lean 4: Cálculo Lambda, Teoría de Tipos Dependientes y Demostración Formal (60 Módulos + 4 Talleres + Mini-Curso TTD + 22 Guías)

[![Lean 4 Kernel CI](https://github.com/LegalIntermediaSL/Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/LegalIntermediaSL/Lean/actions/workflows/ci.yml)
[![GitHub Pages Web](https://github.com/LegalIntermediaSL/Lean/actions/workflows/pages.yml/badge.svg)](https://legalintermediasl.github.io/Lean/)
[![Open in Lean 4 Web Playground](https://img.shields.io/badge/Lean_4_Playground-Ejecutar_Online-blue?logo=lean)](https://live.lean-lang.org/)

Bienvenido a este repositorio enciclopédico y curso práctico de **Lean 4** como **asistente de demostraciones** (*proof assistant*) y **lenguaje de programación funcional dependientemente tipado**, con una cobertura exhaustiva del **Cálculo Lambda ($\lambda$)**, la **Teoría de Tipos Dependientes (MLTT / CIC)** y la **Verificación Formal de Sistemas, Compiladores, Criptografía ZK y Consenso Distribuido**.

---

## 🎓 Mini-Curso Completo de Teoría de Tipos Dependientes (Edición Ampliada de Wikipedia)

Un conjunto estructurado de **11 documentos `.md`** en [`docs/curso_teoria_tipos_dependientes/`](docs/curso_teoria_tipos_dependientes/00_indice_minicurso_ttd.md) que constituye un **mini-curso autocontenido de la Teoría de Tipos Dependientes**, ampliando sección por sección el artículo enciclopédico **[Teoría de Tipos Dependientes (Wikipedia)](https://es.wikipedia.org/wiki/Teor%C3%ADa_de_Tipos_Dependientes)** con reglas de inferencia completas, diagramas, historia, semántica categórica, implementación de verificadores, código Lean 4 ejecutable y ejercicios resueltos:

| Lección | Documento del Mini-Curso | Apartado de Wikipedia Ampliado y Contenido |
| :---: | :--- | :--- |
| **Índice** | [**00_indice_minicurso_ttd.md**](docs/curso_teoria_tipos_dependientes/00_indice_minicurso_ttd.md) | **Portada, Mapa Conceptual y Plan de Estudios** del Mini-Curso de Teoría de Tipos Dependientes |
| **Lección 01** | [**01_introduccion_e_historia_ttd.md**](docs/curso_teoria_tipos_dependientes/01_introduccion_e_historia_ttd.md) | **Introducción e Historia:** ¿Qué es un tipo dependiente? De Russell, Church, BHK y `Automath` a Martin-Löf, Girard y Lean 4; comparativa ZFC vs. TTD |
| **Lección 02** | [**02_juicios_contextos_y_universos.md**](docs/curso_teoria_tipos_dependientes/02_juicios_contextos_y_universos.md) | **Definición Formal I:** Contextos (telescopios $\Gamma$), los 4 juicios de Martin-Löf, **Universos al estilo de Russell vs. Tarski** ($\mathcal{U}_i$ vs. $\text{El}$), familias $B : A \to \mathcal{U}_i$ y las 5 reglas canónicas |
| **Lección 03** | [**03_tipos_pi_funciones_dependientes.md**](docs/curso_teoria_tipos_dependientes/03_tipos_pi_funciones_dependientes.md) | **Definición Formal II — El Tipo $\Pi$:** Producto dependiente $\prod_{x:A} B(x)$, reglas formales, fibraciones y secciones, reducción a $A \to B$, polimorfismo y funciones de aridad variable |
| **Lección 04** | [**04_tipos_sigma_pares_dependientes.md**](docs/curso_teoria_tipos_dependientes/04_tipos_sigma_pares_dependientes.md) | **Definición Formal III — El Tipo $\Sigma$:** Suma dependiente $\sum_{x:A} B(x)$, pares dependientes $\langle a, b \rangle$, `Sigma` vs. `Subtype` vs. `Exists`, y demostración del **Axioma de Elección Constructivo** |
| **Lección 05** | [**05_curry_howard_y_logica_predicados.md**](docs/curso_teoria_tipos_dependientes/05_curry_howard_y_logica_predicados.md) | **Correspondencia de Curry-Howard-Lambek:** Lógica de predicados ($\Pi \leftrightarrow \forall$, $\Sigma \leftrightarrow \exists$), triple adjunción $\Sigma_f \dashv f^* \dashv \Pi_f$ de Lawvere y demostraciones en Lean 4 |
| **Lección 06** | [**06_cubo_lambda_y_sistemas_tipos_puros.md**](docs/curso_teoria_tipos_dependientes/06_cubo_lambda_y_sistemas_tipos_puros.md) | **Sistemas del Cubo Lambda:** Los 3 ejes de Barendregt, Sistemas de Tipos Puros (PTS) y análisis de **$\lambda P$ (LF), $\lambda P2$, $\lambda P\underline{\omega}$ y $\lambda C$ (Cálculo de Construcciones)** |
| **Lección 07** | [**07_igualdad_intensional_extensional_y_hott.md**](docs/curso_teoria_tipos_dependientes/07_igualdad_intensional_extensional_y_hott.md) | **Familias Inductivas, Igualdad y HoTT:** $W$-types, tipo identidad $\text{Id}_A(a,b)$, eliminador $J$, **TTD Intensional vs. Extensional**, UIP/Axioma $K$ y **Univalencia en HoTT** |
| **Lección 08** | [**08_lenguajes_comparativa_y_aplicaciones.md**](docs/curso_teoria_tipos_dependientes/08_lenguajes_comparativa_y_aplicaciones.md) | **Lenguajes con Tipos Dependientes y Proyecto Final:** Comparativa técnica entre **Lean 4, Coq/Rocq, Agda, Idris 2 (QTT), F\*, Twelf y Epigram** + Proyecto Integrador en Lean 4 |
| **Lección 09** | [**09_semantica_categorica_cwf_y_modelos.md**](docs/curso_teoria_tipos_dependientes/09_semantica_categorica_cwf_y_modelos.md) | **Semántica Categórica, CwF y Modelos Cúbicos:** **Categorías con Familias (CwF)** de Dybjer formalizadas en Lean 4, realizabilidad, **Modelo de Grupoides** y **Teoría de Tipos Cúbica (CCHM)** |
| **Lección 10** | [**10_implementacion_typechecker_nbe_y_elaboracion.md**](docs/curso_teoria_tipos_dependientes/10_implementacion_typechecker_nbe_y_elaboracion.md) | **Implementación de un Typechecker y Elaborador:** Índices vs. Niveles de De Bruijn, **Normalización por Evaluación (NbE)**, algoritmo bidireccional de Coquand y **unificación de patrones de Miller** |

---

## 🧭 Rutas de Aprendizaje Recomendadas

* **🟢 Ruta 1 — Empezar desde Cero (Paso a Paso y Didáctica):**
  1. [00_vscode_ecosistema_y_tutoriales.md](docs/00_vscode_ecosistema_y_tutoriales.md) *(Instalar VS Code y entender el Lean Infoview)*
  2. [**M14_DidacticStepByStepProofs.lean**](LeanTT/M14_DidacticStepByStepProofs.lean) *(Tu primera demostración con el estado del Infoview comentado línea a línea)*
  3. [**M15_DidacticDependentTypesFromZero.lean**](LeanTT/M15_DidacticDependentTypesFromZero.lean) *(Tipos dependientes explicados con un restaurante, una cuenta bancaria y un ascensor)*
  4. [16_arbol_decision_tacticas_cheatsheet.md](docs/16_arbol_decision_tacticas_cheatsheet.md) *(Árbol de decisión "¿Qué táctica uso ahora?")*
  5. Talleres prácticos progresivos con solucionarios comentados:
     * [Taller 01 (`E01`)](LeanTT/Exercises/E01_WorkoutLambdaAndLogic.lean) + [Solucionario `S01`](LeanTT/Solutions/S01_WorkoutLambdaAndLogic.lean)
     * [Taller 02 (`E02`)](LeanTT/Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean) + [Solucionario `S02`](LeanTT/Solutions/S02_WorkoutInductiveFamiliesAndEquality.lean)
     * [Taller 03 (`E03`)](LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean) + [Solucionario `S03`](LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean)

* **🔵 Ruta 2 — Fundamentos Matemáticos, Elaborador y Kernel de la Teoría de Tipos Dependientes:**
  1. [**14_tratado_completo_teoria_tipos_dependientes.md**](docs/14_tratado_completo_teoria_tipos_dependientes.md) + [M13_FoundationsOfDependentTypeTheory.lean](LeanTT/M13_FoundationsOfDependentTypeTheory.lean) *(De Frege, Russell, Brouwer y Automath a Martin-Löf, $W$-types y el eliminador $J$)*
  2. [01_calculo_lambda.md](docs/01_calculo_lambda.md) + [M01_LambdaCalculus.lean](LeanTT/M01_LambdaCalculus.lean) + [M16_DidacticLambdaCubeAndPTS.lean](LeanTT/M16_DidacticLambdaCubeAndPTS.lean) *(Las 8 esquinas del Cubo de Barendregt)*
  3. [02_tipos_dependientes_pi_sigma.md](docs/02_tipos_dependientes_pi_sigma.md) $\to$ [03_jerarquia_universos_y_prop.md](docs/03_jerarquia_universos_y_prop.md) $\to$ [05_familias_inductivas_y_recursividad.md](docs/05_familias_inductivas_y_recursividad.md) $\to$ [06_igualdad_transporte_y_hott.md](docs/06_igualdad_transporte_y_hott.md)
  4. [**20_arquitectura_elaborador_bidireccional_y_unificacion.md**](docs/20_arquitectura_elaborador_bidireccional_y_unificacion.md) + [**M40_MiniDependentTypeChecker.lean**](LeanTT/M40_MiniDependentTypeChecker.lean) + [**M50_BidirectionalElaboratorAndUnification.lean**](LeanTT/M50_BidirectionalElaboratorAndUnification.lean) *(Proyectos Cumbre I y II: El Kernel y el Elaborador Bidireccional escritos en Lean 4)*

* **🟣 Ruta 3 — Verificación de Software, Compiladores, Criptografía ZK, Seguridad y Consenso:**
  * Estructuras de datos, refinamientos y algoritmos: `M17` (BST), `M18` (Insertion Sort), `M33` (Regex/Brzozowski), `M34` (Parsers), `M45` (Liquid/Refinement Types), `M48` (Árboles Rojo-Negro de Okasaki).
  * Sistemas, seguridad, políticas y consenso: `M19` (Session Types), `M28` (Tipos Lineales / Rust Borrow Checker), `M29` (Lógica de Separación / `iris-lean`), `M30` (Smart Contracts / `evm-asm`), `M41` (Flujo de Información y No-Interferencia), `M43` (Motor de Autorización estilo AWS Cedar), `M46` (Mónadas Libres y Efectos Algebraicos), `M47` (Consenso Distribuido y Quórums).
  * Compiladores, bases de datos e IA científica: `M20` (Compilador a máquina de pila), `M24` y `M35` (Motor y Optimizador SQL verificado), `M38` (Diferenciación Automática / `SciLean`).
  * Criptografía de Conocimiento Cero y Probabilidad (`Verified-zkEVM`): `M21` (Circuitos R1CS/ZK estilo `Clean`), `M31` (Protocolo Sum-Check estilo `ArkLib`), `M32` (Polinomios computables estilo `CompPoly`), `M42` (Protocolos $\Sigma$ de Schnorr y Simulación HVZK), `M44` (Árboles de Merkle dependientes), `M49` (Distribuciones discretas y Cadenas de Markov estilo `VCV-io`).

---

## 1. Las 21 Monografías y Guías de Referencia (`docs/`)

| Doc | Guía en `docs/` | Contenido Principal |
| :---: | :--- | :--- |
| **00** | [00_vscode_ecosistema_y_tutoriales.md](docs/00_vscode_ecosistema_y_tutoriales.md) | **Lean 4 en VS Code** (Infoview, atajos Unicode, `lake`), **Librerías usuales** (`Mathlib4`, `Batteries`, `Aesop`, `Plausible`, Loogle/Moogle) y **Tutoriales/Libros** |
| **01** | [01_calculo_lambda.md](docs/01_calculo_lambda.md) | $\alpha/\beta/\eta/\delta/\iota/\zeta$-reducción, índices de De Bruijn, combinadores $S, K, I$, numerales de Church, PTS y Cubo de Barendregt |
| **02** | [02_tipos_dependientes_pi_sigma.md](docs/02_tipos_dependientes_pi_sigma.md) | Tipos $\Pi$, Tipos $\Sigma$, intuición geométrica de fibraciones, `HList`, subtipos `{x : A // P x}` y `printf` dependientemente tipado |
| **03** | [03_jerarquia_universos_y_prop.md](docs/03_jerarquia_universos_y_prop.md) | `Sort u`, `Prop` vs `Type u`, Paradoja de Girard/Hurkens, función `imax`, impredicatividad, *Proof Irrelevance* y eliminación de *subsingletons* |
| **04** | [04_curry_howard_y_logica.md](docs/04_curry_howard_y_logica.md) | Trinidad Curry-Howard-Lambek, lógica intuicionista vs clásica (`Classical.em`), traducción de doble negación de Gödel-Gentzen y Teorema de Diaconescu |
| **05** | [05_familias_inductivas_y_recursividad.md](docs/05_familias_inductivas_y_recursividad.md) | Familias inductivas indexadas (`Vec α n`, `Fin n`, `BalTree`), parámetros vs índices, eliminadores `rec`, `noConfusion`, positividad estricta y `WellFounded` |
| **06** | [06_igualdad_transporte_y_hott.md](docs/06_igualdad_transporte_y_hott.md) | Igualdad de Martin-Löf (`Eq`), eliminador $J$ (`Eq.rec`), solución a `"motive is not type correct"`, `HEq`, `funext`, `propext`, cocientes (`Quot`) y UIP vs HoTT |
| **07** | [07_estructuras_clases_y_algebra.md](docs/07_estructuras_clases_y_algebra.md) | Telescopios de De Bruijn, estructuras *Bundled* vs *Semi-Bundled*, herencia diamante, síntesis tabulada de *Typeclasses*, `outParam` y coerciones |
| **08** | [08_tacticas_vs_terminos.md](docs/08_tacticas_vs_terminos.md) | El Criterio de De Bruijn, metavariables, tabla completa Tácticas $\leftrightarrow$ Términos $\lambda$, bloques `calc` y modo `conv` |
| **09** | [09_monadas_y_programacion_funcional.md](docs/09_monadas_y_programacion_funcional.md) | `Functor`, `Applicative`, `Monad`, `LawfulMonad`, desazucarado de `do`, transformadores (`StateT`, `ReaderT`, `ExceptT`) y Perceus |
| **10** | [10_metateoria_stlc_debruijn.md](docs/10_metateoria_stlc_debruijn.md) | Sintaxis intrínsecamente tipada del Cálculo $\lambda$ Simplemente Tipado (STLC) con índices de De Bruijn, debilitamiento, sustitución paralela y evaluador denotacional |
| **11** | [11_metateoria_calculo_lambda_no_tipado.md](docs/11_metateoria_calculo_lambda_no_tipado.md) | Semántica operacional de paso pequeño (*Small-Step*), paso grande (*Big-Step*), Progreso, Preservación y teorema de equivalencia |
| **12** | [12_metaprogramacion_y_kernel.md](docs/12_metaprogramacion_y_kernel.md) | El AST `Lean.Expr` del kernel, `CoreM`/`MetaM`/`TermElabM`/`TacticM`, macros higiénicas, DSLs y creación de tácticas propias |
| **13** | [13_enlaces_webs_proyectos_y_videos.md](docs/13_enlaces_webs_proyectos_y_videos.md) | **Enlaces web importantes** (`lean4.dev`, `lean-lang.org`, **[TauCeti](https://github.com/TauCetiProject/TauCeti)**), **Criptografía ZK / SNARKs** (**[ArkLib](https://github.com/Verified-zkEVM/ArkLib)**, **[VCV-io](https://github.com/Verified-zkEVM/VCV-io)**, **[CompPoly](https://github.com/Verified-zkEVM/CompPoly)**, **[Clean](https://github.com/Verified-zkEVM/clean)**, **[Verified-zkEVM](https://github.com/Verified-zkEVM)**) y **mejores vídeos de YouTube** |
| **14** | [**14_tratado_completo_teoria_tipos_dependientes.md**](docs/14_tratado_completo_teoria_tipos_dependientes.md) | **Tratado Completo de la Teoría de Tipos Dependientes desde Cero:** Historia y antecedentes (Frege, Russell, Brouwer, Church, Automath, Martin-Löf, Girard, Coquand), ZFC vs TTD, las 5 reglas canónicas, tipos $\Pi, \Sigma, W, \text{Id}$ y contractibilidad |
| **15** | [**15_catalogo_40_modulos_y_ambitos.md**](docs/15_catalogo_40_modulos_y_ambitos.md) | **Catálogo General de los 60 Módulos Ejecutables (`M01`–`M60`)** y los 4 talleres de ejercicios (`E01`–`E04`) |
| **16** | [**16_arbol_decision_tacticas_cheatsheet.md**](docs/16_arbol_decision_tacticas_cheatsheet.md) | **Cheat Sheet y Árbol de Decisión de Tácticas** + solución de los 7 errores más comunes de Lean 4 |
| **17** | [**17_guia_migracion_haskell_coq_python_a_lean4.md**](docs/17_guia_migracion_haskell_coq_python_a_lean4.md) | **Guía de Migración a Lean 4** desde Python/TypeScript/Rust, Haskell/OCaml y Coq/Rocq/Agda |
| **18** | [**18_glosario_enciclopedico_teoria_de_tipos.md**](docs/18_glosario_enciclopedico_teoria_de_tipos.md) | **Glosario Enciclopédico A–Z** de Cálculo Lambda, Teoría de Tipos Dependientes y Lean 4 |
| **19** | [**19_verificacion_formal_sistemas_criptografia_y_consenso.md**](docs/19_verificacion_formal_sistemas_criptografia_y_consenso.md) | **Verificación de Sistemas Críticos (`M41`–`M49`):** Flujo de Información (No-Interferencia), Protocolos $\Sigma$, AWS Cedar, Árboles de Merkle, Efectos Algebraicos, Consenso Distribuido y Probabilidad Discreta |
| **20** | [**20_arquitectura_elaborador_bidireccional_y_unificacion.md**](docs/20_arquitectura_elaborador_bidireccional_y_unificacion.md) | **Del Elaborador Bidireccional al Kernel (`M40` + `M50`):** Cómo funcionan `synth` ($\Rightarrow$), `check` ($\Leftarrow$) y las sustituciones de metavariables `?m` antes del Kernel |
| **21** | [**21_compiladores_cps_starks_ltl_y_teoria_juegos.md**](docs/21_compiladores_cps_starks_ltl_y_teoria_juegos.md) | **Compiladores (CPS / SSA / `wp`), LTL, Tipos de Sesión, STARKs/FRI, Teoría de Juegos, Privacidad Diferencial, Reentrancia EVM y el Kernel Polimórfico (`M51`–`M60`)** |

---

## 2. Los 60 Módulos Ejecutables en `LeanTT/` (`M01`–`M60`) + 4 Talleres

| # | Archivo en `LeanTT/` | Bloque / Ámbito | Contenido Práctico y Teoremas Verificados |
| :-: | :--- | :--- | :--- |
| **01** | [M01_LambdaCalculus.lean](LeanTT/M01_LambdaCalculus.lean) | Núcleo $\lambda$ | Reducciones $\beta/\eta/\delta/\iota/\zeta$, combinadores $S, K, I, B, C$, booleanos y numerales de Church |
| **02** | [M02_DependentTypes.lean](LeanTT/M02_DependentTypes.lean) | Núcleo TTD | Familias dependientes, combinador $S$ dependiente, $\Sigma$-types, subtipos y `printf` tipado |
| **03** | [M03_UniversesAndProp.lean](LeanTT/M03_UniversesAndProp.lean) | Universos | `Sort u`, `ULift`, impredicatividad de `Prop`, irrelevancia de prueba y eliminación de subsingletons |
| **04** | [M04_CurryHoward.lean](LeanTT/M04_CurryHoward.lean) | Lógica | Curry-Howard con términos $\lambda$ puros, De Morgan, teorema de Glivenko (`¬¬(P ∨ ¬P)`) y lógica clásica |
| **05** | [M05_InductiveFamilies.lean](LeanTT/M05_InductiveFamilies.lean) | Inductivos | Predicado `EsPar`, ordinales `Fin' n`, vectores `Vec α n` con `get` seguro, `Nat.rec` y `termination_by` |
| **06** | [M06_EqualityAndTransport.lean](LeanTT/M06_EqualityAndTransport.lean) | Igualdad | Simetría/transitividad/congruencia con `Eq.rec`, `funext`, `propext` y construcción de $\mathbb{Z}$ como cociente |
| **07** | [M07_TypeClassesAndAlgebra.lean](LeanTT/M07_TypeClassesAndAlgebra.lean) | Álgebra | Jerarquía `Semigrupo` $\to$ `Monoide` $\to$ `Grupo`, unicidad del neutro, $(a^{-1})^{-1} = a$ y grupo producto |
| **08** | [M08_TacticsAndCalculationalProofs.lean](LeanTT/M08_TacticsAndCalculationalProofs.lean) | Tácticas | Término $\lambda$ vs `by`, fórmula de Gauss con `calc`, reescritura selectiva con `conv`, `simp`, `decide` y `omega` |
| **09** | [M09_MonadsAndEffects.lean](LeanTT/M09_MonadsAndEffects.lean) | Mónadas | Mónada `WriterNat`, demostración de `LawfulMonad`, coste verificado de pasos de Collatz y `ExceptT` + `StateM` |
| **10** | [M10_MetatheorySTLC.lean](LeanTT/M10_MetatheorySTLC.lean) | Metateoría | STLC intrínsecamente tipado con índices de De Bruijn, debilitamiento, sustitución paralela y evaluador denotacional |
| **11** | [M11_OperationalSemantics.lean](LeanTT/M11_OperationalSemantics.lean) | Semántica | Semánticas `BigStep` ($\Downarrow$), `Step` ($\longrightarrow$) y `MultiStep` ($\longrightarrow^*$), determinismo y adecuación |
| **12** | [M12_MetaprogrammingAndTactics.lean](LeanTT/M12_MetaprogrammingAndTactics.lean) | Metaprogramación | ASTs del kernel (`Lean.Expr`), `MetaM`, macros higiénicas, mini-DSL de conjuntos y táctica en `TacticM` |
| **13** | [M13_FoundationsOfDependentTypeTheory.lean](LeanTT/M13_FoundationsOfDependentTypeTheory.lean) | Fundamentos MLTT | *Large Elimination*, `VectorRecursivo`, eliminador $J$, contractibilidad del espacio basado y **$W$-Types** (`WNat`) |
| **14** | [**M14_DidacticStepByStepProofs.lean**](LeanTT/M14_DidacticStepByStepProofs.lean) | **Didáctico 1** | **"Tu Primera Demostración Paso a Paso":** Estado exacto del Infoview (`Γ ⊢ Meta`) comentado antes y después de cada táctica |
| **15** | [**M15_DidacticDependentTypesFromZero.lean**](LeanTT/M15_DidacticDependentTypesFromZero.lean) | **Didáctico 2** | **"Tipos Dependientes Cotidianos":** Menú del restaurante ($\Pi$), caja etiquetada ($\Sigma$), cuenta bancaria sin descubierto y ascensor tipado |
| **16** | [**M16_DidacticLambdaCubeAndPTS.lean**](LeanTT/M16_DidacticLambdaCubeAndPTS.lean) | **Didáctico 3** | **"Las 8 Esquinas del Cubo de Barendregt":** Un ejemplo ejecutable para cada uno de los 8 sistemas ($\lambda^\to$ a $\lambda C$) |
| **17** | [M17_VerifiedDataStructuresBST.lean](LeanTT/M17_VerifiedDataStructuresBST.lean) | Estructuras de Datos | Árboles Binarios de Búsqueda (`BST`), `mirror_mirror`, `mem_bstInsert_self` y `mem_bstInsert_of_mem` |
| **18** | [M18_VerifiedSortingAlgorithms.lean](LeanTT/M18_VerifiedSortingAlgorithms.lean) | Algoritmos | `insertionSort`, predicado inductivo `Sorted` y demostración completa de `sorted_insertionSort` |
| **19** | [M19_FiniteStateMachinesAndProtocols.lean](LeanTT/M19_FiniteStateMachinesAndProtocols.lean) | Protocolos / FSM | Mónada indexada por estados `Protocol s1 s2 α` (*Session Types*) para sesiones de red seguras por construcción |
| **20** | [M20_VerifiedCompilerAndStackMachine.lean](LeanTT/M20_VerifiedCompilerAndStackMachine.lean) | Compiladores | Compilador de expresiones a máquina de pila y demostración formal del **Teorema de McCarthy-Painter** (`compile_correct`) |
| **21** | [M21_NumberTheoryAndCryptography.lean](LeanTT/M21_NumberTheoryAndCryptography.lean) | Criptografía / ZK | Teoría de divisibilidad y verificación de **Soundness & Completeness** de puertas de circuitos R1CS/ZK (bit y multiplexor) |
| **22** | [M22_CategoryTheoryAndFunctors.lean](LeanTT/M22_CategoryTheoryAndFunctors.lean) | Categorías | Categorías dependientes, `Copresheaf`, transformaciones naturales y **demostración completa del Lema de Yoneda** |
| **23** | [M23_HoTTAndHomotopyPaths.lean](LeanTT/M23_HoTTAndHomotopyPaths.lean) | HoTT Sintética | Espacio de caminos `Path α a b` en `Type u`, leyes de $\infty$-grupoide, funtorialidad de `ap`, homotopías y equivalencias `α ≃ₕ β` |
| **24** | [M24_RelationalDatabasesAndTypedSQL.lean](LeanTT/M24_RelationalDatabasesAndTypedSQL.lean) | Bases de Datos SQL | Esquemas tipados, cálculo dependiente de filas `Row s`, `selectWhere`, `crossJoin` y equivalencia de filtros |
| **25** | [M25_ModalAndTemporalLogicDSL.lean](LeanTT/M25_ModalAndTemporalLogicDSL.lean) | Lógica Modal | Marcos de Kripke, operadores $\Box P$ y $\Diamond P$, axioma $K$ y los **3 Teoremas de Correspondencia de Sahlqvist-Kripke** ($T, 4, B$) |
| **26** | [M26_SystemFAndParametricity.lean](LeanTT/M26_SystemFAndParametricity.lean) | Sistema F / ADTs | Tipos existenciales impredicativos (pilas abstractas) y naturalidad paramétrica de Reynolds (*Theorems for Free*) |
| **27** | [M27_NormalizationByEvaluation.lean](LeanTT/M27_NormalizationByEvaluation.lean) | Normalización NbE | Algoritmo completo de **Normalización por Evaluación (NbE)** con términos neutros `Ne`, formas normales `Nf`, `reflect` y `reify` |
| **28** | [M28_SubstructuralAndLinearTypes.lean](LeanTT/M28_SubstructuralAndLinearTypes.lean) | Tipos Lineales | Cálculo $\lambda$ lineal (`A ⊸ B`, `A ⊗ B`) estilo *Rust Borrow Checker* con control estático de uso único de recursos |
| **29** | [M29_SeparationLogicAndHeap.lean](LeanTT/M29_SeparationLogicAndHeap.lean) | Lógica de Separación | Inspirado en `iris-lean`: heaps disjuntos, conjunción separadora `P ∗ Q`, `a ↦ₕ v`, regla del marco y exclusión mutua |
| **30** | [M30_SmartContractsAndEVMState.lean](LeanTT/M30_SmartContractsAndEVMState.lean) | Smart Contracts | Inspirado en `evm-asm`: estado de un token y demostración de **conservación de fondos** y aislamiento de cuentas de terceros |
| **31** | [M31_SumCheckProtocolAndOracles.lean](LeanTT/M31_SumCheckProtocolAndOracles.lean) | Sum-Check / SNARKs | Inspirado en `ArkLib` y `VCV-io`: formalización y demostración de **Completitud Perfecta** del protocolo interactivo *Sum-Check* |
| **32** | [M32_ComputablePolynomialsAndFields.lean](LeanTT/M32_ComputablePolynomialsAndFields.lean) | Álgebra Computable | Inspirado en `CompPoly`: polinomios ejecutables, esquema de Horner y demostración de homomorfismo lineal de evaluación |
| **33** | [M33_AutomataAndBrzozowskiDerivatives.lean](LeanTT/M33_AutomataAndBrzozowskiDerivatives.lean) | Autómatas / Regex | Expresiones regulares, anulabilidad `nullable`, **Derivadas de Brzozowski** `deriv` y teoremas algebraicos de `accepts` |
| **34** | [M34_VerifiedParserCombinators.lean](LeanTT/M34_VerifiedParserCombinators.lean) | Parsers Verificados | Combinadores de parsing, leyes de monoide de `<\|>ₚ` y demostración de decrecimiento estricto de entrada |
| **35** | [M35_SQLQueryOptimizerCorrectness.lean](LeanTT/M35_SQLQueryOptimizerCorrectness.lean) | Optimizador SQL | Fusión de filtros y *Filter Pushdown* sobre `UNION` con demostración de preservación semántica (`evalPlan_optimizePlan`) |
| **36** | [M36_GaloisConnectionsAndLattices.lean](LeanTT/M36_GaloisConnectionsAndLattices.lean) | Conexiones de Galois | Posets, adjunciones $\alpha \dashv \gamma$ para interpretación abstracta, monotonía e identidad triangular $\alpha \circ \gamma \circ \alpha = \alpha$ |
| **37** | [M37_StreamsAndBisimulation.lean](LeanTT/M37_StreamsAndBisimulation.lean) | Coinducción / Streams | Flujos infinitos `StreamInf α`, observaciones `head`/`tail`, ley universal de desplegado `cons_head_tail` y `map` |
| **38** | [M38_VerifiedAutomaticDifferentiation.lean](LeanTT/M38_VerifiedAutomaticDifferentiation.lean) | Diferenciación Auto. | Inspirado en `SciLean`: Números Duales $a + b\varepsilon$ ($\varepsilon^2=0$), regla de Leibniz y corrección de *Forward-Mode AD* |
| **39** | [M39_ProofByReflectionAndBitVectors.lean](LeanTT/M39_ProofByReflectionAndBitVectors.lean) | Prueba por Reflexión | Cómo funcionan las tácticas de normalización algebraica: reificación sintáctica, `flatten` y cierre de metas mediante `rfl` |
| **40** | [**M40_MiniDependentTypeChecker.lean**](LeanTT/M40_MiniDependentTypeChecker.lean) | **Proyecto Cumbre I** | **Un Verificador Nuclear de Tipos Dependientes en Lean 4:** `Expr` unificado, `shift`, `subst`, `whnf` e `inferType` para $\Pi$-types |
| **41** | [M41_InformationFlowAndNonInterference.lean](LeanTT/M41_InformationFlowAndNonInterference.lean) | Flujo de Información | Retículo de seguridad `pub ⊑ₛ sec`, `LowEquiv` y demostración del **Teorema de No-Interferencia** (`non_interference`) |
| **42** | [M42_FiatShamirAndSigmaProtocols.lean](LeanTT/M42_FiatShamirAndSigmaProtocols.lean) | Protocolos $\Sigma$ / ZK | Inspirado en `ArkLib`: Protocolos $\Sigma$ de Schnorr, **Completitud**, **2-Special Soundness** y **Simulador HVZK** |
| **43** | [M43_AuthorizationPolicyEngineCedar.lean](LeanTT/M43_AuthorizationPolicyEngineCedar.lean) | Políticas / AWS Cedar | Inspirado en `cedar-spec`: motor de autorización y pruebas de `default_deny`, `forbid_overrides_permit` y `global_freeze_denies_all` |
| **44** | [M44_MerkleTreesAndCryptographicCommitments.lean](LeanTT/M44_MerkleTreesAndCryptographicCommitments.lean) | Árboles de Merkle | `MerkleTree h` indexado por altura, **Completitud de Pruebas de Inclusión** y reducción de **Binding** a colisiones del hash |
| **45** | [M45_RefinementTypesAndLiquidPredicates.lean](LeanTT/M45_RefinementTypesAndLiquidPredicates.lean) | Tipos de Refinamiento | Estilo Liquid Haskell / F\*: `PosNat`, intervalos `Interval lo hi`, `clamp` verificado y punto medio `midpoint` |
| **46** | [M46_FreeMonadsAndAlgebraicEffects.lean](LeanTT/M46_FreeMonadsAndAlgebraicEffects.lean) | Efectos Algebraicos | Mónada libre `KVProg α`, las 3 leyes de mónada, intérprete `handleState` y ley algebraica *Read-After-Write* |
| **47** | [M47_DistributedConsensusAndQuorums.lean](LeanTT/M47_DistributedConsensusAndQuorums.lean) | Consenso Distribuido | Intersección de quórums honestos (Paxos/Raft/BFT) y demostración de **Acuerdo de Valor Único** (`quorum_agreement`) |
| **48** | [M48_CertifiedRedBlackTreeInvariants.lean](LeanTT/M48_CertifiedRedBlackTreeInvariants.lean) | Árboles Rojo-Negro | Rotaciones de `balance` de Chris Okasaki y demostración formal de preservación de claves (`mem_balance`, `mem_insert`) |
| **49** | [M49_ProbabilityDistributionsAndMarkovChains.lean](LeanTT/M49_ProbabilityDistributionsAndMarkovChains.lean) | Probabilidad Discreta | Inspirado en `VCV-io`: distribuciones ponderadas `Dist α` y conservación de masa total bajo `map`, `scale` y pasos de Markov |
| **50** | [**M50_BidirectionalElaboratorAndUnification.lean**](LeanTT/M50_BidirectionalElaboratorAndUnification.lean) | **Proyecto Cumbre II** | **Elaborador Bidireccional y Metavariables en Lean 4:** `MetaTy`, leyes de sustitución y modos `synth` ($\Rightarrow$) / `check` ($\Leftarrow$) |
| **51** | [M51_ContinuationPassingStyleCPS.lean](LeanTT/M51_ContinuationPassingStyleCPS.lean) | Compiladores CPS | Transformación a *Continuation-Passing Style* (`evalCPS`) y demostración del **Teorema de Plotkin** (`evalCPS e k = k (evalDirect e)`) |
| **52** | [M52_StaticSingleAssignmentAndRegisterAlloc.lean](LeanTT/M52_StaticSingleAssignmentAndRegisterAlloc.lean) | Compiladores SSA | Instrucciones SSA sobre banco de registros y demostración de preservación semántica de *Constant Folding* (`execProg_foldProg`) |
| **53** | [M53_LinearTemporalLogicModelChecking.lean](LeanTT/M53_LinearTemporalLogicModelChecking.lean) | Lógica Temporal LTL | Trazas infinitas, operadores $\bigcirc, \Box, \Diamond, \mathcal{U}$, desplegado en punto fijo $\Box \varphi \leftrightarrow \varphi \land \bigcirc \Box \varphi$ e inducción de invariantes |
| **54** | [M54_ConcurrentProcessCalculusAndSessionDuality.lean](LeanTT/M54_ConcurrentProcessCalculusAndSessionDuality.lean) | Tipos de Sesión | Tipos de sesión binarios de Honda, involutividad `dual (dual s) = s` y progreso libre de *deadlocks* en sincronización de canales |
| **55** | [M55_STARKsAndFRILowDegreeFolding.lean](LeanTT/M55_STARKsAndFRILowDegreeFolding.lean) | zk-STARKs / FRI | Descomposición par-impar de polinomios, operador de plegado `friFold` y colapso simétrico sobre el subgrupo $\{x, -x\}$ |
| **56** | [M56_GameTheoryNashEquilibriumAndVCG.lean](LeanTT/M56_GameTheoryNashEquilibriumAndVCG.lean) | Teoría de Juegos | Demostración formal del **Teorema de Vickrey (DSIC)** (`vickrey_truthful_dominant`) y dominancia en el Dilema del Prisionero |
| **57** | [M57_DifferentialPrivacyAndSensitivity.lean](LeanTT/M57_DifferentialPrivacyAndSensitivity.lean) | Privacidad Diferencial | Sensibilidad $L_1$ de consultas (`HasSensitivity`), subaditividad y comparación de composición paralela ($\max$) vs. secuencial ($+$) |
| **58** | [M58_SmartContractReentrancyAndCEI.lean](LeanTT/M58_SmartContractReentrancyAndCEI.lean) | Anti-Reentrancia EVM | Patrón *Checks-Effects-Interactions* (CEI) + `ReentrancyGuard`, bloqueo de doble retiro reentrante, conservación de fondos y solvencia |
| **59** | [M59_SymbolicExecutionAndWP.lean](LeanTT/M59_SymbolicExecutionAndWP.lean) | Lógica de Hoare / `wp` | Transformador de Precondición Más Débil de Dijkstra (`wp c Q`), `hoareTriple_iff_imp_wp` y verificación de intercambio aritmético *in-place* |
| **60** | [**M60_UniversePolymorphicKernelAndInductives.lean**](LeanTT/M60_UniversePolymorphicKernelAndInductives.lean) | **Proyecto Cumbre III** | **Mini-Kernel CIC con `Sort u`, `imax` y *Large Elimination*:** Impredicatividad de `Prop` y reducción $\iota$ de `boolRec` en tiempo de tipado |
| **E01** | [Exercises/E01_WorkoutLambdaAndLogic.lean](LeanTT/Exercises/E01_WorkoutLambdaAndLogic.lean) | Taller Práctico 01 | Cálculo $\lambda$, lógica constructiva y subtipos + [Solucionario `S01`](LeanTT/Solutions/S01_WorkoutLambdaAndLogic.lean) |
| **E02** | [Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean](LeanTT/Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean) | Taller Práctico 02 | Familias inductivas indexadas `VecE α n`, `head`/`tail` seguros y fusión de `map` + [Solucionario `S02`](LeanTT/Solutions/S02_WorkoutInductiveFamiliesAndEquality.lean) |
| **E03** | [Exercises/E03_WorkoutVerificationAndCryptography.lean](LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean) | Taller Práctico 03 | Puertas aritméticas de circuitos ZK (`NOT`, `AND`, `OR`, `XOR`), polinomios y protocolos $\Sigma$ + [Solucionario `S03`](LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean) |
| **E04** | [Exercises/E04_WorkoutCompilersSTARKsAndGames.lean](LeanTT/Exercises/E04_WorkoutCompilersSTARKsAndGames.lean) | Taller Práctico 04 | Compilación CPS, Lógica Temporal LTL, diferencia simétrica en FRI de STARKs, subasta de Vickrey y `wp` + [Solucionario `S04`](LeanTT/Solutions/S04_WorkoutCompilersSTARKsAndGames.lean) |

---

## Licencia

Distribuido bajo la licencia incluida en [LICENSE](LICENSE).
