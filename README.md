# Lean 4: Cálculo Lambda, Teoría de Tipos Dependientes, Física Matemática e IA Formal (81 Módulos + 6 Talleres + 4 Mini-Cursos + 5 Cuadernos `.ipynb` + 26 Guías)

[![Lean 4 Kernel CI](https://github.com/LegalIntermediaSL/Lean/actions/workflows/ci.yml/badge.svg)](https://github.com/LegalIntermediaSL/Lean/actions/workflows/ci.yml)
[![GitHub Pages Web](https://github.com/LegalIntermediaSL/Lean/actions/workflows/pages.yml/badge.svg)](https://legalintermediasl.github.io/Lean/)
[![Open in Lean 4 Web Playground](https://img.shields.io/badge/Lean_4_Playground-Ejecutar_Online-blue?logo=lean)](https://live.lean-lang.org/)

Bienvenido a este repositorio enciclopédico y curso práctico de **Lean 4** como **asistente de demostraciones** (*proof assistant*) y **lenguaje de programación funcional dependientemente tipado**, con una cobertura exhaustiva del **Cálculo Lambda ($\lambda$)**, la **Teoría de Tipos Dependientes (MLTT / CIC)**, la **Física Matemática y Computación Cuántica** y la **Verificación Formal de Sistemas, Compiladores, Criptografía ZK y Consenso Distribuido**.

---

## 🎓 Mini-Curso I: Teoría de Tipos Dependientes (Edición Ampliada de Wikipedia — 11 Documentos)

Un conjunto estructurado de **11 documentos `.md`** en [`docs/curso_teoria_tipos_dependientes/`](docs/curso_teoria_tipos_dependientes/00_indice_minicurso_ttd.md) que constituye un **mini-curso autocontenido de la Teoría de Tipos Dependientes**, ampliando sección por sección el artículo enciclopédico **[Teoría de Tipos Dependientes (Wikipedia)](https://es.wikipedia.org/wiki/Teor%C3%ADa_de_Tipos_Dependientes)** con reglas de inferencia completas, diagramas, historia, semántica categórica, implementación de verificadores, código Lean 4 ejecutable y ejercicios resueltos:

| Lección | Documento del Mini-Curso I | Apartado de Wikipedia Ampliado y Contenido |
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

## λ Mini-Curso II: Cálculo Lambda, Lógica Combinatoria y Máquinas Abstractas (7 Documentos)

Un segundo mini-curso modular en [`docs/curso_calculo_lambda/`](docs/curso_calculo_lambda/00_indice_minicurso_lambda.md) que amplía los artículos enciclopédicos de **[Cálculo lambda](https://es.wikipedia.org/wiki/C%C3%A1lculo_lambda)** y **[Cálculo lambda tipado](https://es.wikipedia.org/wiki/C%C3%A1lculo_lambda_tipado)**:

| Lección | Documento del Mini-Curso II | Contenido Principal |
| :---: | :--- | :--- |
| **Índice** | [**00_indice_minicurso_lambda.md**](docs/curso_calculo_lambda/00_indice_minicurso_lambda.md) | **Portada y Plan de Estudios** del Mini-Curso de Cálculo Lambda |
| **Lección 01** | [**01_sintaxis_variables_y_debruijn.md**](docs/curso_calculo_lambda/01_sintaxis_variables_y_debruijn.md) | Orígenes (Church 1932), variables libres/ligadas, captura, $\alpha$-equivalencia e **Índices de De Bruijn** en Lean 4 |
| **Lección 02** | [**02_reducciones_beta_eta_y_confluencia.md**](docs/curso_calculo_lambda/02_reducciones_beta_eta_y_confluencia.md) | Las 6 reducciones ($\beta, \eta, \delta, \iota, \zeta, \pi$), estrategias CBN/CBV/Lazy y **Teorema de Confluencia de Church-Rosser** |
| **Lección 03** | [**03_codificaciones_church_scott_y_punto_fijo.md**](docs/curso_calculo_lambda/03_codificaciones_church_scott_y_punto_fijo.md) | **Codificaciones de Church y de Scott** (booleanos, numerales, predecesor de Kleene) y combinadores de punto fijo ($Y, \Theta, Z$) |
| **Lección 04** | [**04_logica_combinatoria_ski_y_abstraccion.md**](docs/curso_calculo_lambda/04_logica_combinatoria_ski_y_abstraccion.md) | **Lógica Combinatoria ($S, K, I, B, C, W$)** de Schönfinkel-Curry y compilador de **Bracket Abstraction** $[x]^*\,t$ en Lean 4 |
| **Lección 05** | [**05_calculo_lambda_tipado_stlc_y_sistema_f.md**](docs/curso_calculo_lambda/05_calculo_lambda_tipado_stlc_y_sistema_f.md) | **STLC ($\lambda^\to$)**, relaciones lógicas de Tait para **Normalización Fuerte**, **Sistema $F$** y **Parametricidad de Reynolds** |
| **Lección 06** | [**06_maquinas_abstractas_krivine_cek_y_nbe.md**](docs/curso_calculo_lambda/06_maquinas_abstractas_krivine_cek_y_nbe.md) | Clausuras, entornos, implementación completa de la **Máquina Abstracta de Krivine (KAM)**, máquina CEK y **NbE** en Lean 4 |

---

## 🔐 Mini-Curso III: Criptografía ZK (SNARKs/STARKs), Post-Cuántica (LWE) y Smart Contracts en Lean 4 (7 Documentos)

Un tercer mini-curso práctico en [`docs/curso_criptografia_zk_lean4/`](docs/curso_criptografia_zk_lean4/00_indice_minicurso_zk_y_cripto.md) conectado con el ecosistema `Verified-zkEVM` (`Clean`, `CompPoly`, `ArkLib`, `VCV-io`):

| Lección | Documento del Mini-Curso III | Contenido Principal |
| :---: | :--- | :--- |
| **Índice** | [**00_indice_minicurso_zk_y_cripto.md**](docs/curso_criptografia_zk_lean4/00_indice_minicurso_zk_y_cripto.md) | **Portada y Mapa Conceptual** del Mini-Curso de Criptografía Verificada y Smart Contracts |
| **Lección 01** | [**01_aritmetizacion_circuitos_r1cs_y_plonk.md**](docs/curso_criptografia_zk_lean4/01_aritmetizacion_circuitos_r1cs_y_plonk.md) | **Aritmetización R1CS / PlonKish:** Bugs *under-constrained* y verificación de *Soundness & Completeness* de puertas y multiplexores |
| **Lección 02** | [**02_polinomios_computables_y_sumcheck.md**](docs/curso_criptografia_zk_lean4/02_polinomios_computables_y_sumcheck.md) | **Polinomios Computables (`CompPoly`)**, Lema de Schwartz-Zippel y **Completitud Perfecta del Protocolo Sum-Check (`ArkLib`)** |
| **Lección 03** | [**03_protocolos_sigma_schnorr_y_fiat_shamir.md**](docs/curso_criptografia_zk_lean4/03_protocolos_sigma_schnorr_y_fiat_shamir.md) | **Protocolos $\Sigma$ (Schnorr):** Demostración en Lean 4 de Completitud, **2-Special Soundness**, **Simulador HVZK** y Fiat-Shamir |
| **Lección 04** | [**04_starks_transparentes_merkle_y_fri.md**](docs/curso_criptografia_zk_lean4/04_starks_transparentes_merkle_y_fri.md) | **zk-STARKs Transparentes:** Árboles de Merkle dependientes y **Ecuación Colineal de Verificación de Ronda de FRI** |
| **Lección 05** | [**05_criptografia_postcuantica_reticulos_lwe.md**](docs/curso_criptografia_zk_lean4/05_criptografia_postcuantica_reticulos_lwe.md) | **Criptografía Post-Cuántica LWE (Regev/Kyber):** Presupuesto de ruido $|e| < q/4$, desencriptado exacto y suma homomórfica |
| **Lección 06** | [**06_verificacion_smart_contracts_evm_y_cei.md**](docs/curso_criptografia_zk_lean4/06_verificacion_smart_contracts_evm_y_cei.md) | **Smart Contracts EVM y Teoría de Juegos:** Conservación de tokens, **Patrón Anti-Reentrancia CEI** y **Subasta de Vickrey (DSIC)** |

---

## ⚛️ Mini-Curso IV: Física Matemática, Mecánica Clásica, Relatividad Especial y Computación Cuántica en Lean 4 (7 Documentos)

Un cuarto mini-curso autocontenido en [`docs/curso_fisica_matematica_lean4/`](docs/curso_fisica_matematica_lean4/00_indice_minicurso_fisica_lean4.md) conectado con **[PhysLean (`HepLean`)](https://github.com/HEPLean/PhysLean)**, **[SciLean](https://github.com/lecopivo/SciLean)** y compiladores cuánticos verificados (**VOQC / SQIR**):

| Lección | Documento del Mini-Curso IV | Contenido Principal |
| :---: | :--- | :--- |
| **Índice** | [**00_indice_minicurso_fisica_lean4.md**](docs/curso_fisica_matematica_lean4/00_indice_minicurso_fisica_lean4.md) | **Portada y Plan de Estudios** del Mini-Curso de Física Matemática y Computación Cuántica |
| **Lección 01** | [**01_analisis_dimensional_y_unidades_dependientes.md**](docs/curso_fisica_matematica_lean4/01_analisis_dimensional_y_unidades_dependientes.md) | **Análisis Dimensional Dependiente (SI):** Grupo abeliano $\mathbb{Z}^7$ en `Quantity d`, seguridad estática de unidades y teorema trabajo-energía |
| **Lección 02** | [**02_mecanica_lagrangiana_accion_y_noether.md**](docs/curso_fisica_matematica_lean4/02_mecanica_lagrangiana_accion_y_noether.md) | **Mecánica Lagrangiana:** Principio de mínima acción de Hamilton ($\delta S = 0 \iff \text{Euler-Lagrange}$) y demostración del **Teorema de Emmy Noether** |
| **Lección 03** | [**03_mecanica_hamiltoniana_poisson_y_simpleticos.md**](docs/curso_fisica_matematica_lean4/03_mecanica_hamiltoniana_poisson_y_simpleticos.md) | **Mecánica Hamiltoniana:** Espacio de fases, **Identidad de Jacobi** en $\mathfrak{sp}(2)$, **Teorema de Liouville** para integradores simplécticos y equilibrio de Boltzmann |
| **Lección 04** | [**04_relatividad_especial_minkowski_y_lorentz.md**](docs/curso_fisica_matematica_lean4/04_relatividad_especial_minkowski_y_lorentz.md) | **Relatividad Especial:** Métrica de Minkowski $\eta_{\mu\nu}$, *boosts* de Lorentz exactos, **invariancia del cono de luz** y barrera sublumínica $|u \oplus_c v| < c$ |
| **Lección 05** | [**05_espacios_hilbert_braket_y_algebra_pauli.md**](docs/curso_fisica_matematica_lean4/05_espacios_hilbert_braket_y_algebra_pauli.md) | **Espacios de Hilbert y Pauli-Clifford:** Enteros de Gauss $\mathbb{Z}[i]$, regla de Born, observables hermíticos ($A^\dagger = A$) y conjugación $H X H = Z$ |
| **Lección 06** | [**06_entrelazamiento_bell_teleportacion_y_compilador_cuantico.md**](docs/curso_fisica_matematica_lean4/06_entrelazamiento_bell_teleportacion_y_compilador_cuantico.md) | **Información Cuántica y Cumbre V:** Prueba formal de **Entrelazamiento de Bell**, **No-Clonación**, **Teleportación Cuántica** y **Gottesman-Knill (`M80`)** |

---

## 🤖📓 Artículo Especial + 5 Cuadernos Ejecutables (`.md` + Jupyter `.ipynb`): Cómo Demostrar Paso a Paso en Lean 4 y Cómo Instruir a una IA

Una guía práctica completa ([**Artículo 24**](docs/24_articulo_anatomia_demostracion_lean4_e_ia.md) + módulo [`M81`](LeanTT/M81_ProofAnatomyAndAIScaffolding.lean) + **5 cuadernos duales** en [`docs/cuadernos_demostracion_e_ia/`](docs/cuadernos_demostracion_e_ia/00_indice_cuadernos_demostracion_e_ia.md) y [`notebooks/`](notebooks/01_del_papel_al_infoview_paso_a_paso.ipynb)) que muestra fotograma a fotograma cómo se construye una demostración en Lean 4 y cómo se instruye a un agente de IA (*Blueprint + Compiler-in-the-Loop + Spec-Audit*) para demostrar sin alucinaciones:

| # | Cuaderno Web (Playground) | Jupyter Notebook (`.ipynb` pre-ejecutado) | Contenido Paso a Paso |
| :-: | :--- | :--- | :--- |
| **Art. 24** | [**24_articulo_anatomia_demostracion_lean4_e_ia.md**](docs/24_articulo_anatomia_demostracion_lean4_e_ia.md) | *(Guía maestra + Plantilla `AGENTS.md`)* | Las 6 fases de una demostración en Lean 4, recorrido completo del **Teorema de Nicómaco**, las **7 reglas operativas para IA** y plantillas copiables |
| **Art. 25** | [**25_estrategia_ia_formalizacion_y_busqueda_pruebas.md**](docs/25_estrategia_ia_formalizacion_y_busqueda_pruebas.md) | *(Arquitectura de Agentes Demostradores)* | Las 4 etapas: puente **Pantograph/LeanDojo/MCP**, **Auto-formalización** (y trampa $x/0=0$), **MCTS vs. Draft-Sketch-Prove (DSP)** y **RAG sobre Mathlib** |
| **01** | [**01_cuaderno_del_papel_al_infoview_paso_a_paso.md**](docs/cuadernos_demostracion_e_ia/01_cuaderno_del_papel_al_infoview_paso_a_paso.md) | [`01_del_papel_al_infoview_paso_a_paso.ipynb`](notebooks/01_del_papel_al_infoview_paso_a_paso.ipynb) | Trazas reales del Infoview con `trace_state`, modo táctico vs. modo término $\lambda$ e inspección de `#print` |
| **02** | [**02_cuaderno_induccion_nicomaco_y_calc.md**](docs/cuadernos_demostracion_e_ia/02_cuaderno_induccion_nicomaco_y_calc.md) | [`02_induccion_teorema_nicomaco_y_calc.ipynb`](notebooks/02_induccion_teorema_nicomaco_y_calc.ipynb) | Especificación sin divisiones truncadas, *Blueprint* de 3 lemas y cadenas `calc` para $\sum k^3 = (\sum k)^2$ |
| **03** | [**03_cuaderno_cuando_la_induccion_falla_generalizacion.md**](docs/cuadernos_demostracion_e_ia/03_cuaderno_cuando_la_induccion_falla_generalizacion.md) | [`03_generalizacion_invariantes_y_acumuladores.ipynb`](notebooks/03_generalizacion_invariantes_y_acumuladores.ipynb) | Reproducción del bloqueo inductivo con acumuladores (`fastRev`) y desbloqueo con `induction ... generalizing acc` |
| **04** | [**04_cuaderno_bucle_ia_compilador_autoreparacion.md**](docs/cuadernos_demostracion_e_ia/04_cuaderno_bucle_ia_compilador_autoreparacion.md) | [`04_bucle_ia_compilador_autoreparacion.ipynb`](notebooks/04_bucle_ia_compilador_autoreparacion.ipynb) | Casos reales de error de `lean` (`omega` no lineal, asociatividad en `rw`, anillos compuestos) y auto-reparación en 2 iteraciones |
| **05** | [**05_cuaderno_plantillas_prompts_agents_y_auditoria.md**](docs/cuadernos_demostracion_e_ia/05_cuaderno_plantillas_prompts_agents_y_auditoria.md) | [`05_prompts_agents_y_auditoria_formal.ipynb`](notebooks/05_prompts_agents_y_auditoria_formal.ipynb) | Detector automático en Python de *reward hacking* (`sorryAx`, `axiom` ilegal, vacuidad) y escaneo global del repositorio |

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

## 1. Las 26 Monografías y Guías de Referencia (`docs/`)

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
| **15** | [**15_catalogo_40_modulos_y_ambitos.md**](docs/15_catalogo_40_modulos_y_ambitos.md) | **Catálogo General de los 81 Módulos Ejecutables (`M01`–`M81`)** y los 6 talleres de ejercicios (`E01`–`E06`) |
| **16** | [**16_arbol_decision_tacticas_cheatsheet.md**](docs/16_arbol_decision_tacticas_cheatsheet.md) | **Cheat Sheet y Árbol de Decisión de Tácticas** + solución de los 7 errores más comunes de Lean 4 |
| **17** | [**17_guia_migracion_haskell_coq_python_a_lean4.md**](docs/17_guia_migracion_haskell_coq_python_a_lean4.md) | **Guía de Migración a Lean 4** desde Python/TypeScript/Rust, Haskell/OCaml y Coq/Rocq/Agda |
| **18** | [**18_glosario_enciclopedico_teoria_de_tipos.md**](docs/18_glosario_enciclopedico_teoria_de_tipos.md) | **Glosario Enciclopédico A–Z** de Cálculo Lambda, Teoría de Tipos Dependientes y Lean 4 |
| **19** | [**19_verificacion_formal_sistemas_criptografia_y_consenso.md**](docs/19_verificacion_formal_sistemas_criptografia_y_consenso.md) | **Verificación de Sistemas Críticos (`M41`–`M49`):** Flujo de Información (No-Interferencia), Protocolos $\Sigma$, AWS Cedar, Árboles de Merkle, Efectos Algebraicos, Consenso Distribuido y Probabilidad Discreta |
| **20** | [**20_arquitectura_elaborador_bidireccional_y_unificacion.md**](docs/20_arquitectura_elaborador_bidireccional_y_unificacion.md) | **Del Elaborador Bidireccional al Kernel (`M40` + `M50`):** Cómo funcionan `synth` ($\Rightarrow$), `check` ($\Leftarrow$) y las sustituciones de metavariables `?m` antes del Kernel |
| **21** | [**21_compiladores_cps_starks_ltl_y_teoria_juegos.md**](docs/21_compiladores_cps_starks_ltl_y_teoria_juegos.md) | **Compiladores (CPS / SSA / `wp`), LTL, Tipos de Sesión, STARKs/FRI, Teoría de Juegos, Privacidad Diferencial, Reentrancia EVM y el Kernel Polimórfico (`M51`–`M60`)** |
| **22** | [**22_qtt_postcuantica_ia_wasm_crdts_y_positividad.md**](docs/22_qtt_postcuantica_ia_wasm_crdts_y_positividad.md) | **Teoría de Tipos Cuantitativa (QTT), Criptografía Post-Cuántica (LWE), IA Segura (ReLU/IBP), WebAssembly, CRDTs, Puertas Cuánticas, Lógica Epistémica, TRS, Hardware y Positividad Estricta (`M61`–`M70`)** |
| **23** | [**23_fisica_matematica_mecanica_clasica_y_cuantica.md**](docs/23_fisica_matematica_mecanica_clasica_y_cuantica.md) | **Física Matemática, Mecánica Lagrangiana/Noether, Geometría Simpléctica, Relatividad de Minkowski, Estadística, Mecánica Cuántica y Gottesman-Knill (`M71`–`M80`)** |
| **24** | [**24_articulo_anatomia_demostracion_lean4_e_ia.md**](docs/24_articulo_anatomia_demostracion_lean4_e_ia.md) | **Artículo Especial: Cómo se Construye una Demostración en Lean 4 Paso a Paso y Cómo se Instruye a una IA (`M81` + 5 Cuadernos `.ipynb`)** |
| **25** | [**25_estrategia_ia_formalizacion_y_busqueda_pruebas.md**](docs/25_estrategia_ia_formalizacion_y_busqueda_pruebas.md) | **Estrategia de la IA para Formalizar Hipótesis:** Puente LSP/MCP (`Pantograph`/`LeanDojo`), Autoformalización, **MCTS vs. Draft-Sketch-Prove (DSP)** y **RAG Mathlib** |

---

## 2. Los 81 Módulos Ejecutables en `LeanTT/` (`M01`–`M81`) + 6 Talleres

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
| **61** | [M61_QuantitativeTypeTheoryQTT.lean](LeanTT/M61_QuantitativeTypeTheoryQTT.lean) | Tipos Cuantitativos QTT | Semianillo de multiplicidades $\{0, 1, \omega\}$ estilo Idris 2 y demostración de **Borrado Estático de Tipos (`scaleCtx_zero_eq_zeroCtx`)** |
| **62** | [M62_PostQuantumLatticeCryptoLWE.lean](LeanTT/M62_PostQuantumLatticeCryptoLWE.lean) | Post-Cuántica LWE | Cifrado basado en retículos *Learning With Errors* (Regev/Kyber), cancelación de máscara y **corrección de desencriptado con ruido acotado** |
| **63** | [M63_VerifiedNeuralNetworkReLURobustness.lean](LeanTT/M63_VerifiedNeuralNetworkReLURobustness.lean) | IA Segura / ReLU IBP | Monotonía e idempotencia de $\text{ReLU}(x)$ y solidez formal de **Interval Bound Propagation (`reluIBP_sound`)** ante perturbaciones |
| **64** | [M64_WebAssemblyStackTypeValidator.lean](LeanTT/M64_WebAssemblyStackTypeValidator.lean) | Máquina Virtual Wasm | Validador estático de pila de tipos WebAssembly y demostración de **Type Soundness (`wasm_instr_type_soundness`)** |
| **65** | [M65_ConflictFreeReplicatedDataTypesCRDT.lean](LeanTT/M65_ConflictFreeReplicatedDataTypesCRDT.lean) | Sistemas CRDTs | Semirretículo `GCounter3` (conmutatividad, asociatividad, idempotencia de `merge`) y **Convergencia Eventual Fuerte** |
| **66** | [M66_ReversibleAndQuantumGateLogic.lean](LeanTT/M66_ReversibleAndQuantumGateLogic.lean) | Puertas Cuánticas | Involutividad reversible de `CNOT`, `Toffoli` y `Fredkin`, conservación de peso de Hamming y **síntesis de `SWAP` con 3 `CNOT`** |
| **67** | [M67_MultiAgentEpistemicLogicS5.lean](LeanTT/M67_MultiAgentEpistemicLogicS5.lean) | Lógica Epistémica $S5_n$ | Conocimiento individual ($K_a$), compartido ($E$) y distribuido ($D$), axiomas $K, T, 4, 5$ y jerarquía $E\varphi \to K_a\varphi \to D\varphi$ |
| **68** | [M68_TermRewritingSystemsAndTermination.lean](LeanTT/M68_TermRewritingSystemsAndTermination.lean) | Reescritura TRS | **Interpretaciones Polinómicas de Lankford** y decrecimiento estricto de la expansión distributiva $a\cdot(b+c) \to a\cdot b + a\cdot c$ |
| **69** | [M69_VerifiedHardwareAdderAndALU.lean](LeanTT/M69_VerifiedHardwareAdderAndALU.lean) | Hardware Digital RTL | Verificación a nivel de puertas booleanas de *Half-Adder*, *Full-Adder* (`fullAdder_correct`) y sumador *Ripple-Carry* (`rippleAdder2_correct`) |
| **70** | [**M70_PatternUnificationAndStrictPositivity.lean**](LeanTT/M70_PatternUnificationAndStrictPositivity.lean) | **Proyecto Cumbre IV** | **Positividad Estricta en el Kernel (`isStrictlyPositive`) y Unificación de Patrones de Miller (`miller_pattern_unification_sound`)** |
| **71** | [M71_DimensionalAnalysisAndSIUnits.lean](LeanTT/M71_DimensionalAnalysisAndSIUnits.lean) | Análisis Dimensional SI | Grupo abeliano $\mathbb{Z}^7$ en `Quantity d`, prevención estática de errores de unidades y **Teorema Trabajo-Energía** |
| **72** | [M72_LagrangianMechanicsAndEulerLagrange.lean](LeanTT/M72_LagrangianMechanicsAndEulerLagrange.lean) | Mecánica Lagrangiana | Principio de Hamilton ($\delta S = 0 \iff \text{Euler-Lagrange}$), **Teorema de Emmy Noether** y oscilador armónico |
| **73** | [M73_HamiltonianMechanicsAndPoissonBrackets.lean](LeanTT/M73_HamiltonianMechanicsAndPoissonBrackets.lean) | Mecánica Hamiltoniana | 2-forma simpléctica, **Identidad de Jacobi** en $\mathfrak{sp}(2)$, **Teorema de Liouville Discreto** y Störmer-Verlet reversible |
| **74** | [M74_SpecialRelativityAndMinkowskiMetric.lean](LeanTT/M74_SpecialRelativityAndMinkowskiMetric.lean) | Relatividad Especial | Métrica de Minkowski $\eta_{\mu\nu}$, *boosts* de Lorentz exactos, **invariancia del cono de luz** y barrera $|u \oplus_c v| < c$ |
| **75** | [M75_StatisticalMechanicsAndEntropy.lean](LeanTT/M75_StatisticalMechanicsAndEntropy.lean) | Mecánica Estadística | Función de partición $Z$, cota del estado fundamental y **equilibrio estacionario bajo Balance Detallado** |
| **76** | [M76_QuantumHilbertSpacesAndBraKet.lean](LeanTT/M76_QuantumHilbertSpacesAndBraKet.lean) | Espacios de Hilbert | Enteros de Gauss $\mathbb{Z}[i]$, Brahmagupta-Fibonacci, notación Bra-Ket y **realidad de valores esperados hermíticos** |
| **77** | [M77_PauliCliffordAlgebraAndUnitarity.lean](LeanTT/M77_PauliCliffordAlgebraAndUnitarity.lean) | Pauli y Clifford | Álgebra de espín ($X Y = i Z$, $\{X, Z\} = 0$), conjugación $H X H = Z, S X S^\dagger = Y$ y conservación unitaria |
| **78** | [M78_QuantumEntanglementAndBellStates.lean](LeanTT/M78_QuantumEntanglementAndBellStates.lean) | Entrelazamiento / Bell | Producto tensorial, invariante de Segre-Schmidt y **demostración formal de entrelazamiento de la base de Bell** |
| **79** | [M79_NoCloningTeleportationAndDeutschJozsa.lean](LeanTT/M79_NoCloningTeleportationAndDeutschJozsa.lean) | Protocolos Cuánticos | **Teorema de No-Clonación**, **Teleportación Cuántica de 3 Qubits** en las 4 ramas y **Algoritmo de Deutsch** |
| **80** | [**M80_VerifiedQuantumCircuitCompilerAndStabilizers.lean**](LeanTT/M80_VerifiedQuantumCircuitCompilerAndStabilizers.lean) | **Proyecto Cumbre V** | **Optimizador Verificado de Circuitos Cuánticos (`denoteCircuit1_optimize1`), síntesis de `CZ` y Teorema de Gottesman-Knill** |
| **81** | [M81_ProofAnatomyAndAIScaffolding.lean](LeanTT/M81_ProofAnatomyAndAIScaffolding.lean) | Demostraciones + IA | **Teorema de Nicómaco** por *Blueprint*, generalización de acumuladores (`fastRev`) y auditoría *Spec-Audit* de no-vacuidad |
| **E01** | [Exercises/E01_WorkoutLambdaAndLogic.lean](LeanTT/Exercises/E01_WorkoutLambdaAndLogic.lean) | Taller Práctico 01 | Cálculo $\lambda$, lógica constructiva y subtipos + [Solucionario `S01`](LeanTT/Solutions/S01_WorkoutLambdaAndLogic.lean) |
| **E02** | [Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean](LeanTT/Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean) | Taller Práctico 02 | Familias inductivas indexadas `VecE α n`, `head`/`tail` seguros y fusión de `map` + [Solucionario `S02`](LeanTT/Solutions/S02_WorkoutInductiveFamiliesAndEquality.lean) |
| **E03** | [Exercises/E03_WorkoutVerificationAndCryptography.lean](LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean) | Taller Práctico 03 | Puertas aritméticas de circuitos ZK (`NOT`, `AND`, `OR`, `XOR`), polinomios y protocolos $\Sigma$ + [Solucionario `S03`](LeanTT/Solutions/S03_WorkoutVerificationAndCryptography.lean) |
| **E04** | [Exercises/E04_WorkoutCompilersSTARKsAndGames.lean](LeanTT/Exercises/E04_WorkoutCompilersSTARKsAndGames.lean) | Taller Práctico 04 | Compilación CPS, Lógica Temporal LTL, diferencia simétrica en FRI de STARKs, subasta de Vickrey y `wp` + [Solucionario `S04`](LeanTT/Solutions/S04_WorkoutCompilersSTARKsAndGames.lean) |
| **E05** | [Exercises/E05_WorkoutQTTPostQuantumAndHardware.lean](LeanTT/Exercises/E05_WorkoutQTTPostQuantumAndHardware.lean) | Taller Práctico 05 | Escalado de contextos en QTT, desencriptado LWE, puntos fijos de ReLU, CRDTs y simetría de *Full-Adder* + [Solucionario `S05`](LeanTT/Solutions/S05_WorkoutQTTPostQuantumAndHardware.lean) |
| **E06** | [Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean](LeanTT/Exercises/E06_WorkoutPhysicsAndQuantumMechanics.lean) | Taller Práctico 06 | Dimensiones SI, Euler-Lagrange inercial, cono de luz relativista, Hadamard y Gottesman-Knill + [Solucionario `S06`](LeanTT/Solutions/S06_WorkoutPhysicsAndQuantumMechanics.lean) |

---

## Licencia

Distribuido bajo la licencia incluida en [LICENSE](LICENSE).
