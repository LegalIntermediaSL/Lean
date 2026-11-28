# Módulo 00: Guía de Lean 4 en Visual Studio Code, Librerías Usuales y Tutoriales

Esta guía práctica cubre todo el flujo de trabajo diario con **Lean 4** en **Visual Studio Code** (y editores compatibles como Cursor o Antigravity), las **librerías principales del ecosistema** (con instrucciones de configuración y búsqueda de teoremas) y los **mejores tutoriales interactivos y libros**.

---

## 1. Uso de Lean 4 en Visual Studio Code

### 1.1 Instalación paso a paso
1. **Instalar Visual Studio Code** desde [code.visualstudio.com](https://code.visualstudio.com/).
2. **Instalar la extensión oficial `lean4`**:
   * Abre el panel de Extensiones (`Cmd+Shift+X` en macOS / `Ctrl+Shift+X` en Windows/Linux).
   * Busca **`lean4`** (publicada por `leanprover`) e instálala.
3. **Instalar `elan` (el gestor de toolchains de Lean)**:
   * Al abrir cualquier archivo `.lean`, la extensión mostrará un botón para instalar `elan` automáticamente, o puedes instalarlo por terminal:
     ```bash
     curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
     ```
4. **Regla de Oro en VS Code — Abrir siempre la Carpeta del Proyecto:**
   * **Nunca** abras un archivo `.lean` suelto con `File -> Open File...` si pertenece a un proyecto con múltiples módulos o dependencias.
   * Usa siempre **`File -> Open Folder...`** seleccionando la carpeta raíz que contiene `lakefile.lean` (o `lakefile.toml`) y `lean-toolchain`. De lo contrario, el servidor de lenguaje de Lean no sabrá dónde encontrar las importaciones ni la caché compilada.

---

### 1.2 El Panel **Lean Infoview**: Tu Laboratorio Interactivo
El **Lean Infoview** es la ventana lateral derecha que se abre automáticamente al editar un archivo `.lean` (o pulsando el icono $\forall$ en la esquina superior derecha). Muestra en tiempo real el estado exacto del verificador de tipos en la posición de tu cursor:

```text
▼ Tactic state
1 goal
α : Type
P Q : α → Prop
h : ∀ (x : α), P x ∧ Q x
x : α
⊢ P x
```

* **Arriba de la línea `⊢` (Turnstile):** Es el **contexto local $\Gamma$** (variables introducidas, hipótesis disponibles y sus tipos).
* **Debajo de `⊢`:** Es la **meta actual (*Goal*)** que debes construir o demostrar en ese punto.
* **Inspección interactiva (*Interactive Term Inspection*):**
  * Si pasas el ratón o haces clic sobre cualquier subexpresión dentro del Infoview, Lean te muestra su tipo implícito y te permite navegar a la definición de cualquier símbolo.
* **Fijar una vista (*Pinning*):**
  * Pulsa el icono de la chincheta (**Pin**) en el Infoview para congelar el estado de una línea mientras mueves el cursor a otra parte del archivo para comparar dos pasos de una demostración.

---

### 1.3 Atajos de Teclado y Símbolos Unicode en VS Code

En Lean 4 los símbolos matemáticos se escriben con una barra invertida `\` seguida de su nombre en LaTeX y pulsando **`Tab`** o **`Espacio`**:

| Para escribir | Teclea en VS Code | Descripción |
| :---: | :--- | :--- |
| `→` | `\to` o `\r` | Flecha de tipo función / implicación |
| `←` | `\l` o `\<-` | Reescritura inversa (`rw [← h]`) o ligadura monádica (`let x ← m`) |
| `↔` | `\iff` o `\lr` | Doble implicación lógica |
| `∀` | `\forall` o `\all` | Cuantificador universal / Tipo $\Pi$ |
| `∃` | `\exists` o `\ex` | Cuantificador existencial |
| `λ` | `\lam` o `\fun` | Abstracción lambda |
| `×` | `\times` o `\x` | Producto cartesiano / Par dependiente |
| `Σ` | `\Sigma` | Suma dependiente ($\Sigma$-type) |
| `∧`, `∨`, `¬` | `\and`, `\or`, `\not` | Conjunción, disyunción y negación |
| `⟨` y `⟩` | `\<` y `\>` | Constructores anónimos (pares, estructuras, existenciales) |
| `▸` | `\t` | Macro de transporte dependiente (`h ▸ px`) |
| `∘` | `\comp` o `\o` | Composición de funciones (`f ∘ g`) |
| `ℕ`, `ℤ`, `ℚ`, `ℝ`, `ℂ` | `\N`, `\Z`, `\Q`, `\R`, `\C` | Conjuntos numéricos en Mathlib4 |
| `α`, `β`, `γ`, `σ`, `τ` | `\a`, `\b`, `\g`, `\s`, `\t` | Variables de tipo griegas |

**Atajos esenciales del editor:**
* `Cmd+Shift+Enter` (macOS) / `Ctrl+Shift+Enter` (Linux/Win): Mostrar/Ocultar el **Lean Infoview**.
* `F12` o `Cmd+Click`: **Ir a la definición** de un teorema, tipo o táctica (incluso dentro del código fuente de Lean o Mathlib).
* `Cmd+Shift+P` $\to$ **`Lean 4: Restart File`**: Reinicia la compilación únicamente del archivo actual (muy útil tras editar macros o importaciones).
* `Cmd+Shift+P` $\to$ **`Lean 4: Refresh File Dependencies`**: Recarga los archivos `.olean` cuando has compilado otros módulos.

---

### 1.4 Comandos Interactivos de Consulta dentro del Editor

Mientras escribes en VS Code, puedes usar estos comandos prefijados por `#` para interrogar a Lean sin salir del archivo (el resultado aparece en el Infoview y subrayado en azul):

```lean
#check Nat.add_comm          -- Muestra la firma/tipo de una constante o teorema
#check (fun x : Nat => x + 1) -- Infiere el tipo de una expresión arbitraria
#eval List.range 10          -- Ejecuta código en la máquina virtual (bytecode rápido)
#reduce (fun x => x + 2) 5   -- Reduce simbólicamente usando el kernel de tipos
#print Nat                   -- Muestra la definición inductiva o el término de prueba completo
#print axioms Classical.em   -- Muestra de qué axiomas depende un teorema (ej. propext, Quot.sound, Classical.choice)
```

**Tácticas de búsqueda asistida en tiempo real:**
Si estás en medio de una prueba (`by ...`) y no recuerdas el nombre del lema:
* **`exact?`**: Busca en todas las librerías importadas un lema que cierre la meta actual en un paso.
* **`apply?`**: Sugiere lemas cuya conclusión unifique con tu meta actual.
* **`rw?`**: Sugiere ecuaciones con las que puedes reescribir tu meta actual.
* **`hint`**: Sugiere qué tácticas podrían avanzar desde el estado actual.

---

### 1.5 Gestión de Proyectos y Dependencias con `lake`

`lake` (*Lean Make*) es el sistema de construcción y gestor de paquetes integrado con Lean 4:

| Comando de Terminal | Función |
| :--- | :--- |
| `lake new mi_proyecto` | Crea un proyecto nuevo desde cero |
| `lake new mi_proyecto math` | Crea un proyecto preconfigurado con **Mathlib4** como dependencia |
| `lake build` | Compila todos los archivos `.lean` del proyecto en binarios verificados `.olean` |
| `lake exe cache get` | **(¡Crucial con Mathlib4!)** Descarga los binarios precompilados de Mathlib4 en segundos para evitar compilarla localmente durante una hora |
| `lake update` | Actualiza las versiones de las dependencias en `lake-manifest.json` |
| `lake clean` | Borra los artefactos compilados en `.lake/build` |

---

## 2. Las Librerías Usuales del Ecosistema Lean 4

### 2.1 `Std` y `Batteries` (`leanprover-community/batteries`)
* **`Std` (incluida en el compilador de Lean 4):** Contiene estructuras de datos eficientes verificadas (`HashMap`, `RBMap`, `BitVec`, `Array`) y tácticas fundamentales (`omega`, `simp`).
* **`Batteries` (antes llamada `Std4`):** Extensión mantenida por la comunidad que añade lemas adicionales sobre listas, arrays, tipos finitos, lógica decidible y utilidades de metaprogramación sin requerir toda la maquinaria matemática de Mathlib.

### 2.2 `Mathlib4` (`leanprover-community/mathlib4`) — La Biblioteca Matemática Unificada
Es una de las mayores proezas de la informática formal moderna (más de **1.6 millones de líneas** de código Lean 4 colaborativo). Contiene:
* **Álgebra:** Teoría de grupos, anillos, cuerpos, módulos, álgebra lineal, teoría de Galois, álgebra homológica (`Mathlib.Algebra.*`, `Mathlib.LinearAlgebra.*`).
* **Análisis y Topología:** Espacios métricos y topológicos, variedades diferenciables, cálculo en espacios de Banach, teoría de la medida e integración de Lebesgue/Bochner (`Mathlib.Topology.*`, `Mathlib.Analysis.*`, `Mathlib.MeasureTheory.*`).
* **Teoría de Números y Combinatoria:** Aritmética modular, números $p$-ádicos, curvas elípticas, grafos (`Mathlib.NumberTheory.*`, `Mathlib.Combinatorics.*`).
* **Teoría de Categorías y Lógica:** Categorías, funtores, adjunciones, límites, categorías monoidales y topos (`Mathlib.CategoryTheory.*`).
* **Tácticas Matemáticas Potentes:**
  * `ring`: Demuestra automáticamente identidades polinómicas en anillos conmutativos (ej. `(x + y)^2 = x^2 + 2*x*y + y^2`).
  * `linarith` / `nlinarith`: Resuelve sistemas de igualdades y desigualdades lineales sobre cuerpos/anillos ordenados.
  * `norm_num`: Evalúa expresiones aritméticas con números grandes, fracciones y primos.
  * `positivity`: Demuestra que una expresión es $> 0$ o $\ge 0$.
  * `abel` / `group`: Normaliza expresiones en grupos abelianos o grupos arbitrarios.
  * `fun_prop` / `continuity` / `measurability`: Demuestra automáticamente que una función compuesta es continua, diferenciable o medible.

**Cómo añadir Mathlib4 a un `lakefile.lean`:**
```text
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"
```
*(Recuerda ejecutar inmediatamente después `lake exe cache get` en tu terminal).*

### 2.3 Motores de Búsqueda para Mathlib4
Dado el tamaño colosal de Mathlib4, la comunidad utiliza cuatro buscadores especializados:
1. **[Loogle (loogle.lean-lang.org)](https://loogle.lean-lang.org/):** Busca teoremas por la **forma sintáctica de su tipo** (por ejemplo, buscar `?a * (?b + ?c)` o `List.replicate`).
2. **[Moogle (moogle.ai)](https://www.moogle.ai/) y [LeanSearch (leansearch.net)](https://leansearch.net/):** Buscadores semánticos en **lenguaje natural** (puedes escribir *"todo subconjunto compacto de un espacio Hausdorff es cerrado"* y te devuelve el teorema exacto de Mathlib4).
3. **[Mathlib4 Docs](https://leanprover-community.github.io/mathlib4_docs/):** Documentación generada con hipervínculos a todas las definiciones y teoremas.

### 2.4 Otras Librerías Destacadas del Ecosistema
* **`Aesop` (`leanprover-community/aesop`):** Táctica de búsqueda automatizada de pruebas mediante árboles AND-OR configurables con reglas (`@[aesop safe]`, `@[aesop unsafe]`).
* **`Plausible` (`leanprover-community/plausible`):** Generador de contraejemplos aleatorios (*Property-Based Testing* al estilo QuickCheck). La táctica `#test` o `plausible` intenta refutar tu teorema con casos de prueba antes de que dediques tiempo a demostrarlo.
* **`ProofWidgets4`:** Librería para renderizar componentes React/HTML interactivos directamente dentro del Lean Infoview (diagramas conmutativos, visualización de grafos y geometría).
* **`Duper`:** Probador automático por superposición de orden superior integrado en Lean 4.
* **`SciLean`:** Computación científica, diferenciación simbólica/automática y optimización numérica en Lean 4.

---

## 3. Tutoriales Interactivos, Juegos y Libros de Referencia

### 3.1 Juegos Interactivos en el Navegador (Sin instalar nada)
* **[Lean 4 Game Server (adam.math.hhu.de)](https://adam.math.hhu.de/):** Plataforma web interactiva con varios juegos graduales:
  1. **The Natural Number Game (NNG4):** Construye la aritmética de Peano y demuestra propiedades de suma, multiplicación y potencias usando `rfl`, `rw` e `induction`.
  2. **Set Theory Game:** Aprende intersecciones, uniones y complementos de conjuntos como proposiciones lógicas.
  3. **Logic Game / Robo:** Aprende las conectivas lógicas mediante acertijos visuales.

### 3.2 Los 4 Libros Oficiales Gratuitos (Con código ejecutable)
1. **[Theorem Proving in Lean 4 (TPiL4)](https://lean-lang.org/theorem_proving_in_lean4/):**
   * *Enfoque:* Teoría de tipos dependientes, cálculo lambda, lógica constructiva/clásica, tipos inductivos, universos y tácticas del núcleo. **(El compañero ideal de este repositorio)**.
2. **[Functional Programming in Lean (FPiL)](https://lean-lang.org/functional_programming_in_lean/):**
   * *Enfoque:* Cómo usar Lean 4 como lenguaje de programación funcional de propósito general: polimorfismo, familias dependientes, mónadas, transformadores, IO y rendimiento.
3. **[Mathematics in Lean (MiL)](https://leanprover-community.github.io/mathematics_in_lean/):**
   * *Enfoque:* Cómo formalizar matemáticas universitarias (álgebra, cálculo, topología, medida) usando **Mathlib4**.
4. **[Metaprogramming in Lean 4](https://leanprover-community.github.io/lean4-metaprogramming-book/):**
   * *Enfoque:* Arquitectura del compilador, manipulación de expresiones `Expr`, mónadas `MetaM`/`TacticM`, elaboración y escritura de DSLs y tácticas propias.

### 3.3 Libros Universitarios Introductorios Adicionales
* **[The Mechanics of Proof](https://hrmacbeth.github.io/math2001/) (Heather Macbeth):** Excelente introducción a las demostraciones matemáticas rigurosas con pruebas calculacionales.
* **[How to Prove It With Lean](https://djvelleman.github.io/HTPIwL/) (Daniel J. Velleman):** Adaptación a Lean 4 del clásico libro *How to Prove It*.
