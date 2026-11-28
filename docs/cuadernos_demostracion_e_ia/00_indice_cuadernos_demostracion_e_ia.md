# Colección de 5 Cuadernos Prácticos: Cómo Demostrar un Teorema en Lean 4 Paso a Paso y Cómo Instruir a una IA

> **Artículo principal de referencia:** [**Artículo 24 — Cómo se Construye una Demostración en Lean 4 Paso a Paso y Cómo se Instruye a una IA para Hacerlo**](../24_articulo_anatomia_demostracion_lean4_e_ia.md)
> **Módulo Lean 4 asociado:** [`LeanTT/M81_ProofAnatomyAndAIScaffolding.lean`](../../LeanTT/M81_ProofAnatomyAndAIScaffolding.lean)

---

## 📓 Doble Formato: Cuadernos Web Interactivos + Jupyter Notebooks (`.ipynb`)

Esta colección está disponible simultáneamente en **dos formatos sincronizados**:
1. **En esta Web Interactiva (Docsify + Lean 4 Web Playground):** cada celda de código Lean 4 incluye los botones `▶ Ejecutar en Lean 4 Web Playground` y `📋 Copiar código` sin instalar nada.
2. **En Jupyter Notebooks (`.ipynb`) ejecutables localmente en VS Code / JupyterLab** (en la carpeta [`notebooks/`](../../notebooks/01_del_papel_al_infoview_paso_a_paso.ipynb)), cuyas celdas invocan en directo el compilador `lean v4.35.0` desde Python y ya incluyen todas las salidas reales del kernel pre-ejecutadas.

---

## 🗺️ Índice de los 5 Cuadernos

| Cuaderno | Versión Web Interactiva | Versión Jupyter Notebook (`.ipynb`) | Objetivo Práctico |
| :---: | :--- | :--- | :--- |
| **Cuaderno 01** | [**01. Del Papel al Infoview Paso a Paso**](01_cuaderno_del_papel_al_infoview_paso_a_paso.md) | [`01_del_papel_al_infoview_paso_a_paso.ipynb`](../../notebooks/01_del_papel_al_infoview_paso_a_paso.ipynb) | Diseccionar fotograma a fotograma el estado del **Lean Infoview** ($\Gamma \vdash G$), transformar metas con `intro`, `rcases`, `have`, `constructor`, `exact` y ver el término $\lambda$ compilado con `#print`. |
| **Cuaderno 02** | [**02. Inducción, Blueprints y `calc` (Nicómaco)**](02_cuaderno_induccion_nicomaco_y_calc.md) | [`02_induccion_teorema_nicomaco_y_calc.ipynb`](../../notebooks/02_induccion_teorema_nicomaco_y_calc.ipynb) | Demostrar desde cero $\sum_{k=0}^n k^3 = (\sum_{k=0}^n k)^2$ aplicando diseño sin divisiones truncadas, descomposición en *Blueprint* de 3 lemas y bloques ecuacionales `calc`. |
| **Cuaderno 03** | [**03. Cuando la Inducción Falla: `generalizing`**](03_cuaderno_cuando_la_induccion_falla_generalizacion.md) | [`03_generalizacion_invariantes_y_acumuladores.ipynb`](../../notebooks/03_generalizacion_invariantes_y_acumuladores.ipynb) | Provocar el bloqueo clásico al verificar una función con acumulador (`fastRev`), leer por qué la hipótesis inductiva es demasiado débil y resolverlo con `induction ... generalizing`. |
| **Cuaderno 04** | [**04. El Bucle IA ↔ Compilador (Auto-Reparación)**](04_cuaderno_bucle_ia_compilador_autoreparacion.md) | [`04_bucle_ia_compilador_autoreparacion.ipynb`](../../notebooks/04_bucle_ia_compilador_autoreparacion.ipynb) | Seguir trazas reales de cómo una IA intenta una prueba, recibe errores exactos de `lean` (`rewrite failed`, `omega`, asociatividad) y repara el código quirúrgicamente en 2 iteraciones. |
| **Cuaderno 05** | [**05. Prompts, `AGENTS.md` y Auditoría Formal**](05_cuaderno_plantillas_prompts_agents_y_auditoria.md) | [`05_prompts_agents_y_auditoria_formal.ipynb`](../../notebooks/05_prompts_agents_y_auditoria_formal.ipynb) | Auditar demostraciones generadas por IA frente a *trampas* sutiles (precondiciones contradictorias/vacuas, axiomas ocultos) con `#print axioms` y certificados de no-vacuidad. |

---

👉 **Empezar por el Cuaderno 01:** [**Cuaderno 01 — Del Papel al Lean Infoview: Tu Primera Demostración Fotograma a Fotograma**](01_cuaderno_del_papel_al_infoview_paso_a_paso.md)
