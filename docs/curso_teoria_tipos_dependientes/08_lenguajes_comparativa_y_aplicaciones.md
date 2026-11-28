# Lección 08: Lenguajes con Tipos Dependientes, Comparativa de Arquitecturas y Proyecto Práctico Integrador

> **Navegación del Mini-Curso:** [⬅️ Lección 07: Igualdad Intensional, Extensional y HoTT](07_igualdad_intensional_extensional_y_hott.md) | [🏠 Índice](00_indice_minicurso_ttd.md) | [➡️ Lección 09: Semántica Categórica, CwF y Modelos](09_semantica_categorica_cwf_y_modelos.md)
>
> **Apartado de Wikipedia ampliado:** Sección *«Lenguajes con tipos dependientes»* (Agda, Coq/Rocq, Idris, Lean, F\*, Epigram, Cayenne, Twelf) en [Teoría de Tipos Dependientes](https://es.wikipedia.org/wiki/Teor%C3%ADa_de_Tipos_Dependientes).
>
> **Módulos ejecutables relacionados:** [`LeanTT/M40_MiniDependentTypeChecker.lean`](../../LeanTT/M40_MiniDependentTypeChecker.lean), [`LeanTT/M50_BidirectionalElaboratorAndUnification.lean`](../../LeanTT/M50_BidirectionalElaboratorAndUnification.lean) y [`docs/17_guia_migracion_haskell_coq_python_a_lean4.md`](../17_guia_migracion_haskell_coq_python_a_lean4.md).

---

## 1. Panorama de los Lenguajes y Asistentes con Tipos Dependientes

El artículo de Wikipedia cierra con un catálogo de los principales lenguajes de programación y asistentes de demostración que implementan la Teoría de Tipos Dependientes. A continuación analizamos en profundidad la arquitectura, teoría subyacente y fortalezas de cada uno de ellos.

### 1.1 Lean 4 (Leonardo de Moura, Sebastian Ullrich y Lean FRO, 2013–Presente)
* **Fundamento teórico:** Cálculo de Construcciones Inductivas (CIC) con jerarquía de universos `Sort u` (`Prop = Sort 0` impredicativo con irrelevancia de prueba definicional, `Type u = Sort (u + 1)` predicativo no acumulativo) + **Tipos Cociente primitivos (`Quot`)**.
* **Rasgo distintivo:** Es simultáneamente un **asistente de demostraciones de vanguardia** (hogar de **`Mathlib4`**, la biblioteca unificada de matemáticas formalizadas más activa del mundo) y un **lenguaje de programación funcional de propósito general compilado a C nativo** con gestión de memoria sin recolector de basura mediante conteo de referencias y reutilización destructiva en el sitio (**Perceus**). El propio compilador y elaborador de Lean 4 están escritos en Lean 4.

### 1.2 Coq / Rocq Prover (INRIA — Coquand, Huet, Paulin-Mohring et al., 1989–Presente)
* **Fundamento teórico:** Cálculo de Construcciones Inductivas Predicativo (pCIC) con universos acumulativos (`Prop`, `SProp`, `Set`, `Type i`) y comprobador de guardas estructurales para inducción y coinducción.
* **Rasgo distintivo:** Pionero de los grandes hitos de la verificación formal industrial y matemática: el compilador de C verificado **CompCert** (Xavier Leroy), la demostración del **Teorema de los Cuatro Colores** y del **Teorema de Feit-Thompson (Orden Impar)** (Georges Gonthier) y el marco de lógica de separación concurrente **Iris**. Extrae código verificado a OCaml, Haskell y Scheme.

### 1.3 Agda (Ulf Norell, Chalmers University, 1999 / Agda 2: 2007–Presente)
* **Fundamento teórico:** Teoría Intuicionista de Tipos de Martin-Löf (MLTT) predicativa intensional, con soporte nativo para **Teoría de Tipos Cúbica (`--cubical`)** donde el Axioma de Univalencia y los tipos inductivos superiores (HITs) se evalúan computacionalmente.
* **Rasgo distintivo:** No utiliza un lenguaje separado de tácticas por defecto: las demostraciones se escriben directamente como **programas funcionales dependientemente tipados** mediante edición interactiva con agujeros (`?` / *holes*), reconocimiento de patrones dependiente (*dependent pattern matching* con cláusulas `with`) y operadores Unicode mixfijos arbitrarios.

### 1.4 Idris 2 (Edwin Brady, University of St Andrews, 2013 / Idris 2: 2020–Presente)
* **Fundamento teórico:** **Teoría de Tipos Cuantitativa (*Quantitative Type Theory*, QTT)** de Bob Atkey y Conor McBride, que anota cada variable del contexto $x :_ρ A$ con una **multiplicidad** $\rho \in \{0, 1, \omega\}$:
  * $\rho = 0$: la variable solo existe en tiempo de compilación (para tipos y pruebas) y se **borra garantizadamente** en tiempo de ejecución (*type erasure*).
  * $\rho = 1$: la variable debe usarse **exactamente una vez** (**tipos lineales** para protocolos de red, ficheros y memoria segura al estilo Rust).
  * $\rho = \omega$: uso irrestricto ordinario.
* **Rasgo distintivo:** Diseñado ante todo para **ingeniería de software de sistemas** con tipos dependientes y tipos de sesión lineales.

### 1.5 F\* (Microsoft Research & INRIA — Nikhil Swamy et al.)
* **Fundamento teórico:** Tipos dependientes combinados con **tipos de refinamiento** (`x : t{P x}`) descargados automáticamente hacia el **SMT solver Z3** y un sistema de efectos monádicos indexados por transformadores de predicados (**Mónadas de Dijkstra**) para verificar código con estado, excepciones y divergencia.
* **Rasgo distintivo:** Usado para verificar la librería criptográfica **HACL\*** / **EverCrypt** (desplegada en el navegador Firefox, el kernel de Linux, Windows y Python).

### 1.6 Otros Lenguajes Históricos y Especializados Mencionados en Wikipedia
* **Automath (N. G. de Bruijn, 1967):** El abuelo de todos los verificadores con tipos dependientes.
* **NuPRL (Robert Constable et al., Cornell, 1985) y RedPRL:** Basados en **Teoría de Tipos Extensional** y semántica computacional de realizabilidad.
* **Twelf (Frank Pfenning y Carsten Schürmann, 1999):** Implementación del marco lógico **LF ($\lambda P$)** con programación lógica de orden superior para demostrar metateoría de lenguajes de programación.
* **Cayenne (Lennart Augustsson, 1998):** Primer lenguaje funcional tipo Haskell con tipos dependientes completos (permitía recursión general sin chequeo de terminación, haciendo el tipado indecidible a cambio de simplicidad).
* **Epigram (Conor McBride y James McKinna, 2004):** Introdujo la programación interactiva bidireccional sobre familias inductivas y la vista de eliminación (`view from the left`).
* **ATS (Hongwei Xi):** Separa estrictamente la fase estática (tipos dependientes y pruebas lineales) de la fase dinámica (compilación directa a C sin sobrecoste).

---

## 2. Tabla Comparativa Técnica de los 6 Grandes Sistemas

| Sistema | Núcleo Teórico | Universo `Prop` e Igualdad | Estilo de Demostración | Gestión de Memoria / Ejecución |
| :--- | :--- | :--- | :--- | :--- |
| **Lean 4** | CIC + `Quot` + `Prop` impredicativo | `Prop` con irrelevancia definicional + UIP + `funext` | Mixto fluido: Términos $\lambda$ + Tácticas (`by`) + Metaprogramación en Lean 4 | Compilación nativa a C con conteo de referencias **Perceus** |
| **Coq / Rocq** | pCIC (Universos acumulativos) | `Prop` impredicativo (sin UIP definicional en `Prop`, sí en `SProp`) | Principalmente por Tácticas (`Ltac2`, `SSReflect`) | VM / `native_compute` y extracción a OCaml / Haskell |
| **Agda** | MLTT Predicativo / Cubical TT (`--cubical`) | Sin `Prop` impredicativo por defecto (tiene `Prop` predicativo opcional); soporta HoTT y Univalencia | Programación funcional directa con *holes* interactivos (sin tácticas) | Compilación vía GHC Haskell o backends JS |
| **Idris 2** | Quantitative Type Theory (QTT: $0, 1, \omega$) | Igualdad intensional en `Type` con borrado cuantitativo ($\rho = 0$) | Programación funcional con tipos lineales + elaborador reflexivo | Compilación nativa vía Chez Scheme / Racket / RefC |
| **F\*** | Tipos Dependientes + Refinamientos + Mónadas Dijkstra | Descarga automática de obligaciones de prueba a **Z3 (SMT)** | Automatización SMT + lemas manuales en estilo funcional | Extracción a OCaml, F#, C (**KaRaMeL**) y WebAssembly |
| **Twelf** | Marco Lógico **LF ($\lambda P$)** | Igualdad sintáctica sobre términos $\beta\eta$-largos (HOAS) | Búsqueda lógica tipo Prolog + verificador de totalidad metateórica | Intérprete en Standard ML |

---

## 3. Proyecto Práctico Integrador del Mini-Curso en Lean 4

Para culminar este Mini-Curso de 8 lecciones, vamos a construir un **micro-proyecto completo y autocontenido en Lean 4** que pone a trabajar juntos **todos los conceptos del artículo de Wikipedia**:
1. Una **familia inductiva indexada** (`Vec α n`).
2. Una **función dependiente ($\Pi$-type)** (`zipWithVec` y `lookupSeguro` con `Fin n`).
3. Un **par dependiente ($\Sigma$-type / `Subtype`)** (`filterSigma`, cuya longitud de salida no se conoce de antemano pero viene certificada por una cota $m \le n$).
4. Una **demostración formal por Curry-Howard y transporte de igualdad ($\text{Id}$)** de que mapear la función identidad sobre cualquier vector de longitud $n$ devuelve el mismo vector (`mapVec_id`).

Todo el código siguiente es 100% válido en **Lean 4** sin ningún `sorry`:

```lean
namespace MiniCursoTTD.ProyectoFinal

universe u v

/-- 1. FAMILIA INDUCTIVA INDEXADA (`Vec α n`):
    Un tipo que depende del valor numérico `n : Nat` (Lecciones 01, 02 y 07). -/
inductive Vec (α : Type u) : Nat → Type u where
  | nil  : Vec α 0
  | cons : α → {n : Nat} → Vec α n → Vec α (n + 1)
  deriving Repr, DecidableEq

/-- 2. TIPO Π (FUNCIÓN DEPENDIENTE):
    `mapVec` transforma cada elemento preservando exactamente el índice de longitud `n`
    en el tipo de salida (Lección 03 y Cubo Lambda λC de la Lección 06). -/
@[simp]
def mapVec {α : Type u} {β : Type v} (f : α → β) : {n : Nat} → Vec α n → Vec β n
  | 0,     .nil       => .nil
  | _ + 1, .cons x xs => .cons (f x) (mapVec f xs)

/-- 3. TIPO Π CON DOS ENTRADAS SINCRONIZADAS POR ÍNDICE (`zipWithVec`):
    El sistema de tipos impide en tiempo de compilación combinar vectores de distinta longitud! -/
@[simp]
def zipWithVec {α β γ : Type} (f : α → β → γ) :
    {n : Nat} → Vec α n → Vec β n → Vec γ n
  | 0,     .nil,       .nil       => .nil
  | _ + 1, .cons x xs, .cons y ys => .cons (f x y) (zipWithVec f xs ys)

/-- 4. TIPO Σ (SUMA DEPENDIENTE CON REFINAMIENTO):
    Cuando filtramos un `Vec α n` con un predicado `p : α → Bool`, no sabemos de antemano
    cuántos elementos sobrevivirán, pero sí sabemos que el resultado es un par dependiente
    `⟨m, ⟨v', h_le⟩⟩` donde `m : Nat`, `v' : Vec α m` y `h_le : m ≤ n`! (Lecciones 04 y 05). -/
def filterVec {α : Type} (p : α → Bool) :
    {n : Nat} → Vec α n → (m : Nat) × Vec α m × PLift (m ≤ n)
  | 0, .nil =>
    ⟨0, .nil, ⟨Nat.le_refl 0⟩⟩
  | _ + 1, .cons x xs =>
    let ⟨m, vCola, ⟨hCola⟩⟩ := filterVec p xs
    if p x then
      ⟨m + 1, .cons x vCola, ⟨Nat.succ_le_succ hCola⟩⟩
    else
      ⟨m, vCola, ⟨Nat.le_succ_of_le hCola⟩⟩

/-- 5. DEMOSTRACIÓN POR CURRY-HOWARD E INDUCCIÓN SOBRE EL TIPO IDENTIDAD (`Id`):
    Para toda longitud `n : Nat` y todo vector `v : Vec α n`, mapear la función identidad
    devuelve exactamente `v` (Lecciones 05 y 07). -/
theorem mapVec_id {α : Type u} : ∀ {n : Nat} (v : Vec α n), mapVec (fun x => x) v = v
  | 0,     .nil       => rfl
  | _ + 1, .cons x xs => congrArg (Vec.cons x) (mapVec_id xs)

end MiniCursoTTD.ProyectoFinal
```

---

## 🎓 ¿Qué Hacer Ahora tras Completar el Mini-Curso?

¡Enhorabuena por completar las 8 lecciones del Mini-Curso de Teoría de Tipos Dependientes! Para seguir profundizando en este repositorio:

1. **Explorar el Kernel y el Elaborador por Dentro:**
   * Estudia cómo se implementa un verificador de tipos dependientes desde cero en [`LeanTT/M40_MiniDependentTypeChecker.lean`](../../LeanTT/M40_MiniDependentTypeChecker.lean) y su elaborador bidireccional en [`LeanTT/M50_BidirectionalElaboratorAndUnification.lean`](../../LeanTT/M50_BidirectionalElaboratorAndUnification.lean) (acompañados de la guía [`docs/20_arquitectura_elaborador_bidireccional_y_unificacion.md`](../20_arquitectura_elaborador_bidireccional_y_unificacion.md)).
2. **Resolver los Talleres de Ejercicios Prácticos:**
   * [`Taller 01 (E01)`](../../LeanTT/Exercises/E01_WorkoutLambdaAndLogic.lean): Cálculo $\lambda$ y lógica constructiva.
   * [`Taller 02 (E02)`](../../LeanTT/Exercises/E02_WorkoutInductiveFamiliesAndEquality.lean): Familias inductivas e igualdad dependiente.
   * [`Taller 03 (E03)`](../../LeanTT/Exercises/E03_WorkoutVerificationAndCryptography.lean): Verificación formal y criptografía de conocimiento cero.
3. **Consultar el Glosario y el Árbol de Decisión de Tácticas:**
   * [`docs/16_arbol_decision_tacticas_cheatsheet.md`](../16_arbol_decision_tacticas_cheatsheet.md)
   * [`docs/18_glosario_enciclopedico_teoria_de_tipos.md`](../18_glosario_enciclopedico_teoria_de_tipos.md)

👉 **Siguiente lección (Ampliación Avanzada):** [**Lección 09 — Semántica Categórica de la Teoría de Tipos Dependientes: Categorías con Familias (CwF), Modelos de Grupoides y Teoría de Tipos Cúbica**](09_semantica_categorica_cwf_y_modelos.md)
