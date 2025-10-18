# AUDIT.md — Auditoría local de RoughBlocks

> **Idiomas**: [English](AUDIT.md) • [Português (Brasil)](AUDIT.pt-BR.md) • **Español**

Esta guía estandariza **cómo auditar localmente** el repositorio `rough-blocks-lean`.
Refleja con precisión el estado actual del proyecto (capas `Defs`,
`Check` y `Scratch` (si están presentes), `External.*`, `Heavy.*` y `Light.*`) sin citar módulos inexistentes.

> Plataformas objetivo: macOS/Linux con `bash`/`zsh`. En Windows, usar **WSL** o **Git Bash**.

---

## ✅ Lista de verificación rápida (TL;DR)

1) **Actualizar dependencias y caché**
```bash
lake update && lake exe cache get
```

2) **Compilar solo lo existente en el repositorio**
```bash
# Heavy (núcleo usado por Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# Certificado/Puente (prestar atención a la capitalización de la ruta)
lake build RoughBlocks.External.BridgeUniform

# Light (facade + especificación/auditoría)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

> **Integración completa (opcional):** Si su `Spec` requiere la existencia,
> también incluya:
> ```bash
> lake build RoughBlocks.Light.Existence
> ```

3) **Auditar axiomas (en el editor de VS Code/Lean)**
Abrir `RoughBlocks/Light/Spec.lean` y ejecutar:

**Esperado:**
- Si `Spec` está en modo *solo fachada*: solo los del sistema
(`propext`, `Classical.choice`, `Quot.sound`).
- Si `Spec` importa la integración completa: además de los del sistema, exactamente `RoughBlocks.Light.budget_verified_by_scan` y
`RoughBlocks.External.bridge_ge_1e6_uniform`.

---

## Prerrequisitos

- **elan/Lean 4** instalado; `lake` debe estar en `PATH`.
- **Git** operativo (para descargar `mathlib` y la caché binaria). - **VS Code** con la extensión Lean4 (recomendado) para inspeccionar axiomas.

### (Opcional) Sincroniza la cadena de herramientas con la versión `mathlib` descargada.
Si observas una discrepancia de versiones:
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
elan toolchain install "$(cat lean-toolchain)"
```

---

## Uso rápido de scripts (recomendado)

El repositorio incluye un script de integración continua (CI) local en `scripts/ci-local.sh`.

```bash
chmod +x ./scripts/ci-local.sh # primera vez
./scripts/ci-local.sh # ejecución predeterminada (Ligero + Intensivo, mejor esfuerzo)
```

**Función:**
1. Asegura la raíz del repositorio y comprueba `lake` en `PATH`.
2. (Opcional) Descarga la caché binaria de mathlib: `lake exe cache get` (tolerante a fallos).

3. **Light (obligatorio):** compila, en el orden sugerido:
`RoughBlocks.Defs`, `RoughBlocks.Check`, `RoughBlocks.External.BridgeUniform`,
`RoughBlocks.Light.Export`, `RoughBlocks.Light.Existence`,
`RoughBlocks.Light.Spec`, `RoughBlocks.Light.Concrete`.
4. (Opcional) ejecuta la demo *scratch* si existe: `lake exe roughblocks_scratch`.
5. Busca `sorry|admit` y **falla** el paso Light si encuentra algo.
6. **Heavy (máximo esfuerzo):** intenta compilar `RoughBlocks.Heavy.*` (los fallos **no** bloquean el script).

### Indicadores admitidos
- `--light` – solo el nivel Light. - `--heavy`: solo el nivel Heavy (no recomendado).
- `--no-cache`: no ejecuta `lake exe cache get`.
- `--no-scratch`: no intenta ejecutar la demo *scratch*.

**Ejemplos:**
```bash
./scripts/ci-local.sh --no-cache --no-scratch
./scripts/ci-local.sh --light
./scripts/ci-local.sh --heavy
```

**Códigos de salida:** `0` (éxito), `2` (*flag* desconocido); otros = fallo del comando subyacente.

El script usa `set -euo pipefail`; la parte **Heavy** es de *mejor esfuerzo* y no provoca el fallo del proceso.

---

## Ejecución manual (sin script)

Si prefieres, ejecuta los comandos directamente:

```bash
# 1) Deps + caché
lake update && lake exe cache get

# 2) Heavy (núcleo usado por Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# 3) (opcional) External/Certificate — útil para comprobar la capitalización en CI
lake build RoughBlocks.External.BridgeUniform

# 4) Light (facade + spec)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

Luego abre `RoughBlocks/Light/Spec.lean` en VS Code y ejecuta `#print axioms`
sobre los símbolos de interés (p. ej., `main_theorem_ge_1e_6`).

> Nota: `RoughBlocks.lean` (si existe) solo importa `Defs` y `Light.Export`.
> Compila “junto” cuando los módulos anteriores compilan; **no** hay un objetivo separado.

---

## Qué comprobar al final

### ✅ Compilar *(en un sistema de archivos que distingue entre mayúsculas y minúsculas)*
- `lake build RoughBlocks.Heavy.Numeric` → **OK**
- `lake build RoughBlocks.Heavy.Buchstab` → **OK**
- `lake build RoughBlocks.External.BridgeUniform` → **OK**
- `lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec` → **OK**

### ✅ Axiomas (en `RoughBlocks/Light/Spec.lean`)
- **Modo "Solo fachada"** *(Spec **no** importa `Light.Existence` ni el certificado)*:

Se esperan **solo** los del sistema: `propext`, `Classical.choice`, `Quot.sound`.
- **Modo de "integración completa"** *(La especificación importa `Light.Existence` y `External.BridgeUniform`)*:

Además de los axiomas del sistema, se esperan **exactamente** estos dos axiomas externos (reproducibles):
- `RoughBlocks.Light.budget_verified_by_scan`
- `RoughBlocks.External.bridge_ge_1e6_uniform`

### ✅ (Opcional) Prueba de humo
Si el ejecutable *scratch* existe:
```bash
lake exe roughblocks_scratch
```
Comprobar el acceso mediante (`RoughBlocks.Light.*`, `LB`, `margin`, `marginR`) y el teorema
(`main_theorem_ge_1e6`).

---

## Solución de problemas (FAQ)

**“No existe el archivo o directorio… RoughBlocks/External/BridgeUniform.lean” (o un módulo similar)**
Usas un sistema de archivos que distingue entre mayúsculas y minúsculas (CI/Linux) o un perfil de compilación antiguo. Prueba:

```bash
# Corregir mayúsculas en la ruta de importación:
# RoughBlocks/External/BridgeUniform.lean (no: external)

# Compilación local recomendada (sin ejecutar la demo "scratch"):
chmod +x ./scripts/ci-local.sh
./scripts/ci-local.sh --no-scratch

# o flujo manual mínimo
lake update && lake exe cache get
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

**“token inesperado 'export'” / “token inesperado 'open'” en `RoughBlocks.lean`**
En Lean4, estos comandos no se reexportan globalmente como se espera. Mantenga **solo** la importación y use nombres completos como `RoughBlocks.Light.*`.

**Los alias causan `dependsOnNoncomputable` / reducibilidad**.
Evite usar `def/abbrev` al principio, ya que apunta a símbolos `noncomputable` de Light.
Prefiera usar nombres completos en los clientes: `RoughBlocks.Light.LB`, etc.

**Divergencia entre la cadena de herramientas y la caché**
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
elan toolchain install "$(cat lean-toolchain)"
lake update && lake exe cache get
```

**Windows**
Use **WSL** o **Git Bash**:
```bash
bash ./scripts/ci-local.sh --no-scratch
```
---

## CI (ejemplo de GitHub Actions)

```yaml
- name: Deps + caché
  run: lake update && lake exe cache get

- name: Hacer ejecutable el script
  run: chmod +x ./scripts/ci-local.sh

- name: Build (Light + Heavy, sin scratch)
  run: ./scripts/ci-local.sh --no-scratch
```
En CI es habitual **desactivar** el paso de *scratch* (`--no-scratch`) y **sincronizar la toolchain/caché** antes de compilar.

---

## Política de estabilidad de la API

- La capa **Light** es la **facade oficial**.  
- Los clientes **no** deben importar `Heavy.*` directamente.  
- `RoughBlocks.lean` (si existe) se mantiene minimalista e importa solo `Defs` + `Light.Export`.

---

## 🔒 Licencias

- **Código**: Apache License 2.0 — ver [`LICENSE`](LICENSE) y [`NOTICE`](NOTICE).
- **Documentación / artículos / imágenes**: CC BY-NC-ND 4.0 — ver [`LICENSE-docs-CC-BY-NC-ND`](LICENSE-docs-CC-BY-NC-ND.es-ES).

> Resumen: el código es abierto y apto para colaboración (Apache-2.0); el texto científico y las figuras permanecen protegidos bajo CC BY-NC-ND.

> Si necesitas permiso para uso comercial u obras derivadas, contacta a los autores.

---

```md
## 📎 Referencia rápida

```bash
# (primera vez) hacer el script ejecutable
chmod +x ./scripts/ci-local.sh

# Ejecución predeterminada (Light + Heavy best-effort)
./scripts/ci-local.sh

# Solo Light
./scripts/ci-local.sh --light

# Solo Heavy (best-effort)
./scripts/ci-local.sh --heavy

# Omitir la descarga de la caché binaria de mathlib
./scripts/ci-local.sh --no-cache

# No ejecutar el ejecutable de demostración (Scratch)
./scripts/ci-local.sh --no-scratch

# Flujo manual reproducible (sin el script)
lake update && lake exe cache get \
  && lake build RoughBlocks.Heavy.Numeric \
  && lake build RoughBlocks.Heavy.Buchstab \
  && lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```