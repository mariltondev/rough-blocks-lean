# RoughBlocks — Lean 4
[![Lean CI](https://github.com/mariltondev/rough-blocks-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/mariltondev/rough-blocks-lean/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/mariltondev/rough-blocks-lean.svg?label=release)](https://github.com/mariltondev/rough-blocks-lean/releases)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17137291.svg)](https://doi.org/10.5281/zenodo.17137291)

> **Estado:** versión pública estable `v1.0.0`
> **Toolchain:** `leanprover/lean4:v4.23.0` · **mathlib:** `v4.23.0` (anclado vía `lean-toolchain`)

> **Idiomas:** Español · [Português (Brasil)](README.pt-BR.md) · [English](README.md)

---

Este repositorio ofrece una formalización completa en Lean 4 del teorema *RoughBlocks* sobre números $m$-ásperos cercanos a $m^2$.  
Incluye el núcleo analítico (`Heavy`), el puente certificado externo (`External`) y la interfaz pública estable (`Light`).

La prioridad es mantener la capa **Light** estable y auditable, con pruebas en Lean
sin depender de axiomas más allá de los “del sistema” (p. ej., `propext`, `Classical.choice`, `Quot.sound`).

**Resultado principal:** para todo $m \ge 10^6$ y $x \le 8$,  
cada bloque $K_x = \{m^2 + xm + 1, \dots, m^2 + (x{+}1)m\}$  
contiene al menos un número $m$-áspero ($P^-(n) > m$).

---

## Resumen
Mostramos que, para todo $m \ge 10^6$ y cada $x \in \{0,\dots,8\}$, el bloque
$K_x=\{m^2+xm+1,\dots,m^2+(x+1)m\}$ contiene al menos un número $m$‑áspero
($P^-(n)>m$). La prueba combina la identidad y la función de Buchstab $\omega$ con
la forma explícita de Mertens mediante la suma de Abel, obteniendo un lema local uniforme en
intervalos cortos $[X,X+Y]$, com $X\in[y^2,y^3]$ e $y\le Y\le 2y$:

![Inequality](docs/img/formula01.svg)

Con constantes efectivas $C_0\le 2$, $C_1\le 4{,}4$ y $C_2=100$. Tratamos el borde $X=y^2$
por separado y eliminamos términos de frontera mediante la convención $\omega(u)=0$ para $0<u<1$.
Aplicando el lema local con $y=Y=m$ y $X=m^2+xm$, obtenemos el resultado para cada $K_x$.

Con las constantes actuales, los **cálculos numéricos sugieren** que el mismo argumento ya funcionaría a partir de
$m\ge 18{,}794$; sin embargo, en este repositorio **certificamos formalmente** $m\ge 10^6$ y cubrimos $2\le m<10^6$
mediante un barrido computacional **reproducible** (código, registros e instrucciones
[aquí](https://doi.org/10.5281/zenodo.17137291)).

### Integración con la formalización en Lean y certificados

- **Franja finita $2 \le m < 10^6$:** encapsulada por un único axioma
  `RoughBlocks.Light.budget_verified_by_scan`, sustentado por un cribado determinista
  (artefactos en [Zenodo — DOI: 10.5281/zenodo.17137291](https://doi.org/10.5281/zenodo.17137291)).

- **Franja asintótica $m \ge 10^6$:** el “puente” que compara la cota inferior analítica $LB(m,x)$
  con el conteo real en el bloque $K_x$ se valida **uniformemente** mediante un certificado en Julia
  con aritmética intervalar (256 bits), almacenado en
  `certs/uniform-bridge-ge-1e6.json` y generado por
  `external/julia/uniform_bridge_certificate.jl`. Este certificado se importa en Lean por el axioma
  `RoughBlocks.External.bridge_ge_1e6_uniform`.

---

## Introducción

Estudiamos números $m$‑ásperos (esto es, $P^-(n)>m$) en ventanas cortas cercanas a $m^2$. Este repositorio aísla el núcleo técnico que sustenta un programa más amplio — en adelante apodado “[`Conjetura de MariltonCR de los primos encajados`](https://doi.org/10.5281/zenodo.16734582)”. El presente trabajo es completamente *incondicional*: demostramos un resultado local uniforme que garantiza, para $m$ grande, la presencia de un $m$‑áspero en cada uno de nueve bloques consecutivos de longitud $m$ inmediatamente a la derecha de $m^2$.

En trabajos paralelos desarrollamos las implicaciones combinatorias y de cribado de este marco para cerrar algunas conjeturas clásicas: la **Hipótesis de Legendre**, la **Conjetura de Oppermann**, la **Conjetura de Brocard** (en la forma “$\ge 4$ primos entre $n^2$ y $(n{+}1)^2$”), la **Conjetura fuerte de Goldbach** (condicional a versiones reforzadas del programa), así como rederivar el **Postulado de Bertrand** como corolario. En paralelo, abrimos una línea de estudio que conecta estas técnicas con heurísticas de cribado bajo la **Hipótesis de Riemann Generalizada (GRH)**.

Estas metas son deliberadamente ambiciosas: ya las presentamos como una hoja de ruta de investigación, y hay enlaces a este repositorio. Aquí entregamos el primer ladrillo técnico — un teorema local con constantes explícitas — sobre el cual se están construyendo las siguientes etapas en preprints separados, con evoluciones periódicas.

## Mapeo entre el artículo y la formalización en Lean

### Repositorio del proyecto (GitHub)
**Repo:** [`github.com/mariltondev/rough-blocks-lean`](https://github.com/mariltondev/rough-blocks-lean)

**PDF del artículo (para auditoría):** [`docs/primos_encaixados_acad.pdf`](docs/primos_encaixados_acad.pdf)

### Módulos actualmente en el repositorio
- `RoughBlocks/Defs.lean` — definiciones básicas: `mRough`, `K`, `BlockHasMRough`.
- `RoughBlocks/Heavy/Numeric.lean` — capa analítica usada por Light:
  - `LB : ℕ → ℕ → ℝ`
  - `margin : ℕ → ℝ`
  - `marginR : ℝ → ℝ`
  - teorema `budget_conservative_formal`.
- `RoughBlocks/Heavy/Buchstab.lean` — **agregador** con identidades/recuentos de Buchstab para `Φ`; lema `PhiGE_mono_in_X` (usado por `Light.Spec`).
- `RoughBlocks/External/BridgeUniform.lean` — axioma externo `bridge_ge_1e6_uniform` (importa el certificado JSON y expone el puente uniforme).
- `RoughBlocks/Light/Export.lean` — *fachada* pública; reexporta la API demostrada y expone `main_theorem_ge_1e6`.
- `RoughBlocks/Light/Spec.lean` — objetivo de auditoría (`#print axioms`) y enganche para la monotonía de $Φ$.
- `RoughBlocks/Check.lean` — (opcional) sanidad de API: ejemplos de tipos y **lemas centinela** que fallan si cambia la superficie pública.

## 🔧 Prerrequisitos

- `elan` (gestor de toolchains de Lean) y `lake` en el `PATH`.
- Git (para descargar `mathlib` y su caché).
- macOS/Linux con `bash`/`zsh` (Windows: WSL o Git Bash).

**Sugerencia (macOS):**
```bash
brew install elan-init
elan toolchain install v4.23.0
```

El archivo `lean-toolchain` del proyecto fija la versión:
```
leanprover/lean4:v4.23.0
```

---

## 🗂️ Estructura del proyecto (esencial)

```
RoughBlocks.lean                 # Punto de entrada minimalista (importa Defs + Light.Export)
RoughBlocks/Defs.lean            # Definiciones básicas: mRough, K, BlockHasMRough

RoughBlocks/Heavy/Numeric.lean   # Núcleo numérico usado por Light (sin axiomas externos)
RoughBlocks/Heavy/Buchstab.lean  # Identidades de Buchstab (discreto y en ventana; agregador)

RoughBlocks/External/BridgeUniform.lean  # Importa el certificado JSON (puente uniforme ≥ 1e6) para Light

RoughBlocks/Light/Export.lean    # Fachada pública: reexporta la API formal demostrada
RoughBlocks/Light/Spec.lean      # Especificación/auditoría (hooks + #print axioms)

scripts/ci-local.sh              # CI local (Light obligatoria + Heavy best-effort; flags --light/--heavy/--no-cache/--no-scratch)
AUDIT.md                         # Guía de auditoría
```

---

## 🚀 Inicio rápido (build)

Actualiza dependencias y caché:
```bash
lake update && lake exe cache get
```

Compila **solo** lo que existe en el repositorio actual:
```bash
# External (certificado uniforme ≥ 1e6)
lake build RoughBlocks.External.BridgeUniform

# Heavy (núcleo usado por Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# Light (fachada + spec/auditoría)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec

# Sanidad de la API (archivo centinela; compila en silencio)
lake build RoughBlocks.Check
```

Auditoría completa vía script:
```bash
chmod +x scripts/ci-local.sh      # primera vez
./scripts/ci-local.sh             # ejecución por defecto (Light + Heavy best-effort)

# variaciones útiles:
./scripts/ci-local.sh --light
./scripts/ci-local.sh --heavy
./scripts/ci-local.sh --no-cache
./scripts/ci-local.sh --no-scratch
```

---

## 🧰 API pública (capa Light)

Importa la fachada y usa nombres calificados del espacio de nombres **Light**:

```lean
import RoughBlocks.Light.Export

-- Usa nombres calificados (recomendado):
#check RoughBlocks.Light.LB
#check RoughBlocks.Light.margin
#check RoughBlocks.Light.marginR
#check RoughBlocks.Light.budget_conservative_formal
#check RoughBlocks.Light.main_theorem_ge_1e6
```

**Teorema listo para usar** (expuesto en `Light.Export`):

```lean
theorem RoughBlocks.Light.main_theorem_ge_1e6
  {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
  RoughBlocks.Light.LB m x ≥ 1
```

**Ejemplo “sanity”** (compacto):

```lean
import RoughBlocks.Light.Export

example {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
    RoughBlocks.Light.LB m x ≥ 1 :=
  RoughBlocks.Light.main_theorem_ge_1e6 (m:=m) (x:=x) hm hx
```

> La capa Light **reexporta** símbolos demostrados en Heavy. Los clientes **no deben**
> importar `RoughBlocks.Heavy.*` directamente — conserva el encapsulamiento.

---

## 🧪 Auditoría de axiomas

Abre `RoughBlocks/Light/Spec.lean` y ejecútalo en el editor:

**Esperado (OK):** solo `propext`, `Classical.choice`, `Quot.sound`.

Consulta también la guía `AUDIT.md` y el script `scripts/ci-local.sh`.

---

## 📚 Módulos actualmente en el repositorio

- `RoughBlocks/Defs.lean` — definiciones básicas:  
  `mRough`, `K`, `BlockHasMRough`,  
  `roughSetInBlock`, `countRoughInBlock`,  
  lema existencial `exists_of_count_ge_one`.

- `RoughBlocks/Check.lean` — sanidad de API (ejemplos centinela).
- `RoughBlocks/Scratch.lean` — ejecutable de demostración (objetivo `roughblocks_scratch`).

- `RoughBlocks/Heavy/Buchstab/Core.lean` — primitivos combinatorios:  
  `isRoughGT`, `isRoughGE`, `PhiGT`, `PhiGE`, `primesIn`,  
  instancias decidibles y lemas básicos usados en las identidades.

- `RoughBlocks/Heavy/Buchstab/MinFac.lean` — capa fina sobre `Nat.minFac`:  
  lemas `minFac_prime_of_two_le`, `minFac_le_of_prime_dvd`, `minFac_dvd_eq`.

- `RoughBlocks/Heavy/Buchstab.lean` — **(opcional)** agregador que reexporta el núcleo de Buchstab.

- `RoughBlocks/Heavy/WindowLink/Core.lean` — “ventana $ (N_1,N_2] \leftrightarrow $ diferencia de $\Phi$”:  
  `PhiGE_diff_window_eq`, `PhiGE_diff_window_ge`, `PhiGE_diff_window_ge_div`,  
  `sum_card_eq_sum_diff_phiGE`.

- `RoughBlocks/Heavy/WindowLink/Block.lean` — puente bloque $\leftrightarrow$ ventana (caso $p:=m{+}1$):  
  `countRoughInBlock_as_window`,  
  `strict_window_card_eq_phiDiff_succ` y versión en $\mathbb{R}$,  
  `countRoughInBlock_eq_phiDiff_succ_real`.

- `RoughBlocks/Heavy/Identity.lean` — identidades de Buchstab (global y en ventana):  
  `buchstab_identity_PhiGT`, `buchstab_identity_window_core`, `countWindow_as_sumDiff_real`,  
  versión con $1\le X$; equivalencias `mRough`↔`isRoughGT` para $n\ge 1$;  
  `isRoughGT_iff_isRoughGE_succ_of_two_le`; monotonía `PhiGE_mono_in_X`.

- `RoughBlocks/Heavy/Numeric.lean` — capa analítica/conservadora **(sin axiomas externos)**:  
  `LB : ℕ → ℕ → ℝ`, `margin : ℕ → ℝ`, `marginR : ℝ → ℝ`,  
  lema `LB_ge_margin'`, hitos `margin_ge_one_at_1e6` y `margin_ge_one_from_1e6`,  
  teorema `budget_conservative_formal` ($m \ge 10^6$).

- **Módulos auxiliares (partes analíticas):**  
  `RoughBlocks/Heavy/Bridge.lean`  
  `RoughBlocks/Heavy/Interface.lean`  
  `RoughBlocks/Heavy/Log10Bounds.lean`  
  `RoughBlocks/Heavy/Omega.lean`

- `RoughBlocks/Light/Concrete.lean` — traducciones concretas/auxiliares usadas en el enunciado público.
- `RoughBlocks/Light/Existence.lean` — versión unificada del teorema de existencia (capa Light);  
  **axioma externo** `budget_verified_by_scan` (franja $2\le m<10^6,0\le x\le 8$).

- `RoughBlocks/Light/Export.lean` — *fachada* pública; reexporta la API demostrada:  
  incluye enunciados objetivo para uso externo, p. ej., `main_theorem_ge_1e6` y `budget_main`.

- `RoughBlocks/Light/Spec.lean` — objetivo de auditoría (`#print axioms`);  
  consolida dependencias externas visibles en la capa `Light`.

- `RoughBlocks/External/BridgeUniform.lean` — axioma externo `bridge_ge_1e6_uniform`;  
  importa el certificado de Julia (JSON) y lo expone como puente uniforme en la formalización.

### Observación

Este proyecto utiliza **dos dependencias externas reproducibles**; todo lo demás se demuestra internamente en Lean, usando solo los axiomas “del sistema” (`propext`, `Classical.choice`, `Quot.sound`).

- **Franja finita $2 \le m < 10^6$.**  
  Encapsulada por el axioma `RoughBlocks.Light.budget_verified_by_scan`
  (archivo `RoughBlocks/Light/Existence.lean`), sustentada por un cribado determinista
  (código, registros e instrucciones en [Zenodo — DOI: 10.5281/zenodo.17137291](https://doi.org/10.5281/zenodo.17137291)).  
  En particular, para $2 \le m < 10^6$ y $0 \le x \le 8$, se tiene $\mathrm{LB}(m,x) \ge 1$.

- **Franja asintótica $m \ge 10^6$.**  
  El “puente” que compara la cota inferior analítica $LB(m,x)$ con el conteo real en el bloque $K_x$
  se valida **uniformemente** mediante el axioma `RoughBlocks.External.bridge_ge_1e6_uniform`
  (archivo `RoughBlocks/External/BridgeUniform.lean`), instanciado por un certificado en Julia con
  aritmética intervalar de 256 bits, almacenado en `certs/uniform-bridge-ge-1e6.json`
  y generado por `external/julia/uniform_bridge_certificate.jl`.

---

## Mapa Paper ↔ Lean (1×1)

| Concepto | LaTeX (stub) | Lean (tipo) |
|---|---|---|
| "n es m-rough (todo primo de n es > m)" | mRough(m,n) | `RoughBlocks.mRough m n : Prop` |
| Bloque K(m,x) | {m^2 + xm + 1, ..., m^2 + (x+1)m} | `RoughBlocks.K m x : Finset ℕ` |
| "K tiene algún m-rough" | ∃ n ∈ K(m,x): mRough(m,n) | `RoughBlocks.BlockHasMRough m x : Prop` |
| Límite inferior | LB(m,x) ≥ 1 (condiciones en m,x) | `RoughBlocks.Light.LB m x ≥ 1` *(reexportado en `Light.Export`)* |
| Monotonía (ejemplo) | Φ_p(N1) ≤ Φ_p(N2) si N1 ≤ N2 | `PhiGE_mono_in_X p : Monótona (fun N => PhiGE N p)` |
| Buchstab (ventana) | ∑_p (Φ((X+Y)/p) - Φ(X/p)) | véanse los lemas en `Heavy/Buchstab/Core` y `Heavy/WindowLink/Core` *(véase también `Heavy/Identity.lean`)* |

> Nota: la notación de Lean usa `Nat`, `Finset` y `BigOperators` de `mathlib`.  
> Las versiones en $\mathbb{R}$ surgen por coerción (`Nat.cast_*`) combinada con monotonía.

---

## 🧭 Política de estabilidad de la API

- **Light** es la **fachada oficial** (superficie pública estable).  
  - Garantizamos **compatibilidad retroactiva** dentro del mismo *major* para los nombres bajo `RoughBlocks.Light.*`.
  - Las rupturas de API ocurren solo en **versiones major** y se documentarán en las *release notes*.

- **Heavy** (`RoughBlocks.Heavy.*`) y **External** (`RoughBlocks.External.*`) son **detalles internos**.  
  - Los clientes **no deben** importarlos directamente. Estas capas pueden cambiar sin aviso.

- `RoughBlocks.lean` es **minimalista** (importa solo `Defs` + `Light.Export`) y no añade API propia.  
  - Usa siempre la fachada: `import RoughBlocks.Light.Export`.

- `Light/Spec.lean` es **solo para auditoría** (`#print axioms`) y **no** forma parte de la API pública.

- Las **depreciaciones** en la capa Light se anunciarán con un período de transición y rutas de migración en las *release notes*.

---

## 🧩 Ejemplos mínimos de uso

```lean
import RoughBlocks.Light.Export
import RoughBlocks.Defs

-- Usa nombres cortos solo de la capa Light
open RoughBlocks.Light

example {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
    LB m x ≥ 1 :=
  main_theorem_ge_1e6 (m:=m) (x:=x) hm hx

-- Consultando predicados de Defs:
#check RoughBlocks.mRough    -- ℕ → ℕ → Prop
#check RoughBlocks.K         -- ℕ → ℕ → Finset ℕ
#check RoughBlocks.BlockHasMRough
```

---

## 🐛 Solución de problemas (FAQ)

- **Toolchain divergente / caché de mathlib**  
  ```bash
  cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
  elan toolchain install "$(cat lean-toolchain)"
  lake update && lake exe cache get
  ```

- **Errores al intentar reexportar con `export`/`open (...)` al inicio**  
  Mantén el punto de entrada simple (solo `import`); usa nombres calificados
  `RoughBlocks.Light.*` en los módulos cliente.

- **Aliases `abbrev/def` a elementos `noncomputable`**  
  Evita “reflejar” símbolos de Light en la parte superior de `RoughBlocks` para no caer en
  `dependsOnNoncomputable`/reducibility. Usa nombres calificados.

---

## 🔒 Licencias

- **Código**: Apache License 2.0 — ver [`LICENSE`](LICENSE) y [`NOTICE`](NOTICE).
- **Documentación / artículos / imágenes**: CC BY-NC-ND 4.0 — ver [`LICENSE-docs-CC-BY-NC-ND`](LICENSE-docs-CC-BY-NC-ND.pt-BR).

> Resumen: el código es abierto y colaborativo (Apache‑2.0); el texto científico y las figuras están protegidos bajo CC BY‑NC‑ND.

> Si necesitas permiso para uso comercial u obras derivadas, contacta a los autores.

---

### 🔎 Documentos de auditoría
- English: [`AUDIT.md`](AUDIT.md)
- Português (Brasil): [`AUDIT.pt-BR.md`](AUDIT.pt-BR.md)
- Español: [`AUDIT.es.md`](AUDIT.es.md)

---

## 🤝 Contribuir

- Mantenemos **Light** estable; los cambios internos en **Heavy** deben preservar las firmas
  expuestas por `Light.Export` (o coordinarse con *release notes*).  
- Para nuevos módulos, añade verificaciones de auditoría en `Light/Spec.lean` cuando tenga sentido.

---

## 🧪 CI (sugerencia)

```yaml
- name: Deps + Cache
  run: lake update && lake exe cache get

- name: Build Heavy
  run: |
    lake build RoughBlocks.Heavy.Numeric
    lake build RoughBlocks.Heavy.Buchstab

- name: Build External Bridge
  run: lake build RoughBlocks.External.BridgeUniform

- name: Build Light
  run: lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

---

## 📎 Referencia rápida

```bash
# (primera vez) hacer ejecutable el script
chmod +x ./scripts/ci-local.sh

# Ejecución por defecto (Light + Heavy best-effort)
./scripts/ci-local.sh

# Solo Light
./scripts/ci-local.sh --light

# Solo Heavy (best-effort)
./scripts/ci-local.sh --heavy

# Sin descargar la caché binaria de mathlib
./scripts/ci-local.sh --no-cache

# No ejecutar el ejecutable de demostración (Scratch)
./scripts/ci-local.sh --no-scratch

# Flujo manual reproducible (sin el script)
lake update && lake exe cache get \
  && lake build RoughBlocks.Heavy.Numeric \
  && lake build RoughBlocks.Heavy.Buchstab \
  && lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```