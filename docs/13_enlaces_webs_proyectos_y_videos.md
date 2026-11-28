# Módulo 13: Directorio de Webs Esenciales, Proyectos de Vanguardia (TauCeti, Verified-zkEVM) y los Mejores Vídeos de YouTube sobre Lean 4

Esta guía recopila los **portales oficiales**, **plataformas interactivas**, **repositorios de investigación puntera** (en inteligencia artificial matemática, criptografía de conocimiento cero ZK/SNARKs y verificación de sistemas) y **los mejores vídeos, cursos y conferencias en YouTube** para aprender y profundizar en **Lean 4**.

---

## Índice del Documento
1. [Portales Oficiales y Plataformas de Aprendizaje Web](#1-portales-oficiales-y-plataformas-de-aprendizaje-web)
2. [Buscadores de Teoremas, Paquetes y Comunidad](#2-buscadores-de-teoremas-paquetes-y-comunidad)
3. [Proyectos de Frontera: Matemáticas Colaborativas IA + Humanos (`TauCeti`)](#3-proyectos-de-frontera-matemáticas-colaborativas-ia--humanos-tauceti)
4. [Criptografía Formal, SNARKs y Verificación de Sistemas (`Verified-zkEVM`)](#4-criptografía-formal-snarks-y-verificación-de-sistemas-verified-zkevm)
5. [Grandes Hitos de Formalización en Lean 4 (Matemáticas e Industria)](#5-grandes-hitos-de-formalización-en-lean-4-matemáticas-e-industria)
6. [Los Mejores Vídeos, Cursos y Canales de YouTube sobre Lean 4](#6-los-mejores-vídeos-cursos-y-canales-de-youtube-sobre-lean-4)

---

## 1. Portales Oficiales y Plataformas de Aprendizaje Web

| Sitio Web | Enlace Directo | Descripción y Utilidad Principal |
| :--- | :--- | :--- |
| **Lean 4 Learning Hub** | [https://lean4.dev](https://lean4.dev) | Plataforma moderna de aprendizaje de Lean 4 con guías paso a paso sobre sintaxis, programación funcional, tácticas, uso de `lake`, ejercicios y recursos estructurados. |
| **Sitio Oficial de Lean** | [https://lean-lang.org](https://lean-lang.org) | Portal oficial del lenguaje Lean y de la **Lean FRO** (*Focused Research Organization*). Incluye documentación oficial, manuales de referencia, descargas y noticias de versiones. |
| **Lean Community** | [https://leanprover-community.github.io](https://leanprover-community.github.io) | Portal central de la comunidad matemática de Lean y **Mathlib4**: guías de instalación, estadísticas de formalización, eventos, blogs y hojas de trucos (*cheat sheets*). |
| **Lean 4 Web Playground** | [https://live.lean-lang.org](https://live.lean-lang.org) | Editor de Lean 4 completo en el navegador con Mathlib4 precargado. Ideal para probar código y compartir enlaces reproducibles sin instalar nada localmente. |
| **Lean Game Server** | [https://adam.math.hhu.de](https://adam.math.hhu.de) | Servidor de juegos interactivos en el navegador (*The Natural Number Game*, *Set Theory Game*, *Logic Game*, *Linear Algebra Game*). |
| **Lean FRO** | [https://lean-fro.org](https://lean-fro.org) | Organización sin ánimo de lucro fundada por Leonardo de Moura y Sebastian Ullrich para el desarrollo sostenible del compilador de Lean 4 y su infraestructura. |

---

## 2. Buscadores de Teoremas, Paquetes y Comunidad

* **[Lean Reservoir (reservoir.lean-lang.org)](https://reservoir.lean-lang.org):** El registro oficial de paquetes y librerías del ecosistema Lean 4 indexado para `lake`.
* **[Loogle (loogle.lean-lang.org)](https://loogle.lean-lang.org):** Buscador sintáctico por tipos y patrones de expresiones en Mathlib4 (ej. buscar `List.map (?f ∘ ?g)`).
* **[Moogle (moogle.ai)](https://www.moogle.ai) y [LeanSearch (leansearch.net)](https://leansearch.net):** Buscadores semánticos en lenguaje natural para encontrar lemas de Mathlib4 describiendo el enunciado matemático.
* **[Documentación de Mathlib4](https://leanprover-community.github.io/mathlib4_docs/):** Referencia API hipervinculada de todos los módulos de Mathlib4.
* **[Lean Zulip Chat (leanprover.zulipchat.com)](https://leanprover.zulipchat.com):** El foro en tiempo real donde se reúne toda la comunidad mundial de Lean (desde principiantes en `#new members` hasta medallistas Fields e ingenieros del compilador).

---

## 3. Proyectos de Frontera: Matemáticas Colaborativas IA + Humanos (`TauCeti`)

* **[TauCeti (`TauCetiProject/TauCeti`)](https://github.com/TauCetiProject/TauCeti)** *(Web oficial: [https://taucetiproject.org](https://taucetiproject.org))*
  * **¿Qué es?** Una biblioteca abierta y colaborativa de matemáticas formalizadas en Lean 4 (construida sobre Mathlib4 e incubada por la Lean FRO y la Mathlib Initiative) donde **contribuidores de Inteligencia Artificial realizan la implementación y la revisión por pares** bajo la dirección de hojas de ruta (*roadmaps*) escritas por matemáticos humanos.
  * **Cómo funciona:** Los matemáticos humanos definen la arquitectura conceptual y los teoremas objetivo (`TauCetiRoadmap`), mientras que agentes autónomos de IA escriben las demostraciones formales y agentes revisores adversarios evalúan la calidad del código antes de integrarlo, con la garantía absoluta de que el **kernel de Lean 4** verifica cada demostración.

---

## 4. Criptografía Formal, SNARKs y Verificación de Sistemas (`Verified-zkEVM`)

La organización **[Verified-zkEVM](https://github.com/Verified-zkEVM)** desarrolla uno de los ecosistemas más avanzados del mundo en Lean 4 para la **verificación formal de pruebas de conocimiento cero (Zero-Knowledge Proofs / SNARKs)**, polinomios computables, máquinas virtuales criptográficas y lógica de separación:

* **[ArkLib (`Verified-zkEVM/ArkLib`)](https://github.com/Verified-zkEVM/ArkLib):**
  * **Argumentos de conocimiento formalmente verificados en Lean 4**, la biblioteca núcleo para **SNARKs**.
  * Formaliza reducciones de oráculo interactivas (*Interactive Oracle Reductions* — IOR), el protocolo *sum-check*, compromisos polinómicos (*polynomial commitments*), protocolos de proximidad **FRI / STIR / WHIR**, la transformación de **Fiat–Shamir** y la transformación **BCS**.
* **[VCV-io (`Verified-zkEVM/VCV-io`)](https://github.com/Verified-zkEVM/VCV-io):**
  * **Framework de oráculos en Lean 4 para demostraciones criptográficas basadas en juegos** (*game-based cryptographic proofs*), y dependencia esencial de **ArkLib**.
  * ArkLib lo utiliza para modelar adversarios probabilísticos y consultas a oráculos, así como para ejecutar formalmente los argumentos de salto entre juegos (*game-hopping*) en los que se basan las pruebas de seguridad de los SNARKs.
* **[CompPoly (`Verified-zkEVM/CompPoly`)](https://github.com/Verified-zkEVM/CompPoly):**
  * **Polinomios y cuerpos finitos computables**, el núcleo ejecutable de **ArkLib** y un espejo computable de muchas de las definiciones y funciones de **[Mathlib4](https://github.com/leanprover-community/mathlib4)**.
  * Todo en `CompPoly` es **100% computable (ejecutable)**, pero las demostraciones pueden seguir realizándose utilizando las definiciones teóricas correspondientes de Mathlib4 mediante transferencia a través de equivalencias formalmente demostradas.
* **[Clean (`Verified-zkEVM/clean`)](https://github.com/Verified-zkEVM/clean):**
  * **Un DSL de circuitos ZK en Lean 4**. Puede utilizarse tanto para construir circuitos de conocimiento cero (*Zero-Knowledge circuits*) de alta seguridad directamente en Lean como a modo de framework de especificación y verificación formal de circuitos ZK.
* **Más proyectos en la organización [Verified-zkEVM](https://github.com/Verified-zkEVM):**
  * **[iris-lean (`Verified-zkEVM/iris-lean`)](https://github.com/Verified-zkEVM/iris-lean):** Formalización en Lean 4 del framework **Iris** de lógica de separación concurrente de orden superior.
  * **[evm-asm (`Verified-zkEVM/evm-asm`)](https://github.com/Verified-zkEVM/evm-asm):** Semántica formal y verificación de ensamblador para máquinas virtuales (EVM / zkEVM) en Lean 4.

---

## 5. Grandes Hitos de Formalización en Lean 4 (Matemáticas e Industria)

* **[Polynomial Freiman-Ruzsa (PFR) — Terence Tao, Yael Dillies, Bhavik Mehta et al.](https://github.com/teorth/pfr):** Formalización completa en Lean 4 de la conjetura de Marton en combinatoria aditiva en apenas tres semanas de colaboración masiva.
* **[Fermat's Last Theorem (FLT) — Kevin Buzzard et al.](https://github.com/ImperialCollegeLondon/FLT):** Proyecto en curso en el Imperial College London para formalizar en Lean 4 la demostración de Wiles-Taylor del Último Teorema de Fermat.
* **[Prime Number Theorem And More — Alex Kontorovich & Terence Tao](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd):** Formalización del Teorema de los Números Primos y análisis complejo en Lean 4.
* **[Cedar (`cedar-policy/cedar-spec`) — Amazon Web Services](https://github.com/cedar-policy/cedar-spec):** El lenguaje de políticas de autorización de AWS (que protege servicios como Amazon Verified Permissions), cuyo modelo de seguridad y validador están **escritos y demostrados formalmente en Lean 4**.
* **[PhysLean (anteriormente HepLean — `HEPLean/PhysLean`)](https://github.com/HEPLean/PhysLean):** Proyecto colaborativo abierto para formalizar en Lean 4 la **Física Matemática y Teórica**, desde análisis dimensional, mecánica clásica y relatividad especial (grupo de Lorentz y tensores de Minkowski) hasta electromagnetismo, mecánica cuántica y cancelación de anomalías en el Modelo Estándar.
* **[SciLean (`lecopivo/SciLean`)](https://github.com/lecopivo/SciLean):** Biblioteca de computación científica, diferenciación automática verificada y resolución de sistemas variacionales y hamiltonianos en Lean 4.

---

## 6. Los Mejores Vídeos, Cursos y Canales de YouTube sobre Lean 4

### 6.1 Conferencias Magistrales y Visión General (Imprescindibles)
1. **Leonardo de Moura — *"Lean: Past, Present, and Future"* / *"An Introduction to Lean 4"*:**
   * Presentaciones del creador de Lean explicando cómo Lean 4 unifica un asistente de pruebas basado en tipos dependientes con un compilador funcional rápido (gestión de memoria Perceus, metaprogramación extensible y automatización).
   * [Buscar conferencias de Leonardo de Moura en YouTube](https://www.youtube.com/results?search_query=Leonardo+de+Moura+Lean+4)
2. **Terence Tao — *"Machine Assisted Proof"* (Simons Foundation / JMM / IMO Lectures):**
   * Cómo Lean 4, los *blueprints* colaborativos y la IA están transformando la investigación matemática contemporánea.
   * [Ver charlas de Terence Tao sobre Lean en YouTube](https://www.youtube.com/results?search_query=Terence+Tao+Machine+Assisted+Proof+Lean)
3. **Kevin Buzzard — *"What is the point of computers in pure mathematics?"* & *"The Future of Mathematics"*:**
   * Charlas vibrantes, accesibles y llenas de humor sobre por qué la formalización en Lean es el futuro de las matemáticas puras.
   * [Ver charlas de Kevin Buzzard en YouTube](https://www.youtube.com/results?search_query=Kevin+Buzzard+Lean+mathematics)

### 6.2 Canales Oficiales y Series de Cursos Completos en YouTube
1. **[Canal Oficial `leanprover-community` en YouTube](https://www.youtube.com/@leanprovercommunity):**
   * Contiene las grabaciones de todas las conferencias **Lean Together**, **Lean for the Curious Mathematician (LFTCM)**, tutoriales de Mathlib4, metaprogramación en Lean 4 y demostraciones en vivo (como la infinitud de los números primos).
2. **[Xena Project (Imperial College London — Kevin Buzzard)](https://www.youtube.com/@xenaproject4625):**
   * Sesiones prácticas resolviendo teoremas de álgebra, topología, teoría de grupos y teoría de números en Lean paso a paso.
3. **Talleres *"Lean for the Curious Mathematician"* (LFTCM):**
   * Listas de reproducción completas desde cero absoluto hasta formalización de estructuras algebraicas, categoría y análisis en Mathlib4:
   * [Buscar listas de reproducción LFTCM en YouTube](https://www.youtube.com/results?search_query=Lean+for+the+Curious+Mathematician+Lean+4)
4. **Tutoriales Prácticos de Programación Funcional y Tácticas en Lean 4:**
   * Recorridos en vídeo por *The Natural Number Game 4*, *Theorem Proving in Lean 4* y creación de proyectos con `lake` en VS Code:
   * [Buscar tutoriales prácticos de Lean 4 en YouTube](https://www.youtube.com/results?search_query=Lean+4+tutorial+theorem+proving)
