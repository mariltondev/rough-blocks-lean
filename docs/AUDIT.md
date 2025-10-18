# AUDIT.md — Local audit for RoughBlocks

> **Languages**: **English** • [Português (Brasil)](AUDIT.pt-BR.md) • [Español](AUDIT.es-ES.md)

This guide standardizes **how to locally audit** the `rough-blocks-lean` repository.
It accurately reflects the current state of your project (`Defs`,
`Check`, and `Scratch` layers — when present —, `External.*`, `Heavy.*`, and `Light.*`) — without citing non-existent modules.

> Target platforms: macOS/Linux with `bash`/`zsh`. On Windows, use **WSL** or **Git Bash**.

---

## ✅ Quick Checklist (TL;DR)

1) **Update dependencies and cache**
```bash
lake update && lake exe cache get
```

2) **Compile only what exists in the repository**
```bash
# Heavy (core used by Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# Certificate/Bridge (pay attention to path capitalization)
lake build RoughBlocks.External.BridgeUniform

# Light (facade + specification/audit)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

> **Full integration (optional):** If your `Spec` requires the existence,
> also include:
> ```bash
> lake build RoughBlocks.Light.Existence
> ```

3) **Audit axioms (in the VS Code/Lean editor)**
Open `RoughBlocks/Light/Spec.lean` and run:

**Expected:**
- If `Spec` is in *facade-only* mode: only the system ones
(`propext`, `Classical.choice`, `Quot.sound`).
- If `Spec` imports the full integration: in addition to the system ones, exactly
`RoughBlocks.Light.budget_verified_by_scan` and
`RoughBlocks.External.bridge_ge_1e6_uniform`.

---

## Prerequisites

- **elan/Lean 4** installed; `lake` must be in the `PATH`.
- **Git** operational (to download `mathlib` and the binary cache).
- **VS Code** with the Lean4 extension (recommended) to inspect axioms.

### (Optional) Synchronize the toolchain with the downloaded `mathlib`
If you notice a version mismatch:
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
elan toolchain install "$(cat lean-toolchain)"
```

---

## Quick script usage (recommended)

The repository includes a local CI script in `scripts/ci-local.sh`.

```bash
chmod +x ./scripts/ci-local.sh # first time
./scripts/ci-local.sh # default execution (Light + Heavy best-effort)
```

**What it does:**
1. Ensures the repository root and checks `lake` in the `PATH`.
2. (Optional) downloads the mathlib binary cache: `lake exe cache get` (fault-tolerant).
3. **Light (required):** compiles, in the suggested order:
`RoughBlocks.Defs`, `RoughBlocks.Check`, `RoughBlocks.External.BridgeUniform`,
`RoughBlocks.Light.Export`, `RoughBlocks.Light.Existence`,
`RoughBlocks.Light.Spec`, `RoughBlocks.Light.Concrete`.
4. (Optional) runs the *scratch* demo if it exists: `lake exe roughblocks_scratch`.
5. Looks for `sorry|admit` and **fails** the Light step if it finds anything.
6. **Heavy (best-effort):** attempts to compile `RoughBlocks.Heavy.*` (failures **do not** crash the script).

### Supported Flags
- `--light` – only the Light tier.
- `--heavy` – only the Heavy tier (not recommended).
- `--no-cache` – does not run `lake exe cache get`.
- `--no-scratch` – does not attempt to run the *scratch* demo.

**Examples:**
```bash
./scripts/ci-local.sh --no-cache --no-scratch
./scripts/ci-local.sh --light
./scripts/ci-local.sh --heavy
```

**Exit codes:** `0` (success), `2` (unknown *flag*); others = failure of the underlying command.

The script uses `set -euo pipefail`; the **Heavy** part is *best-effort* and does not fail the process.

---

## Manual run (without the script)

If you prefer, run the commands directly:

```bash
# 1) deps + cache
lake update && lake exe cache get

# 2) Heavy (core used by Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# 3) (optional) External/Certificate — useful for checking capitalization in CI
lake build RoughBlocks.External.BridgeUniform

# 4) Light (facade + spec)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

Then open `RoughBlocks/Light/Spec.lean` in VS Code and run `#print axioms`
on the symbols of interest (e.g., `main_theorem_ge_1e6`).

> Note: `RoughBlocks.lean` (if present) only imports `Defs` and `Light.Export`.
> It builds “alongside” when the modules above build; **there isn’t** a separate target.

---

## What to check at the end

### ✅ Build *(in case-sensitive FS)*
- `lake build RoughBlocks.Heavy.Numeric` → **OK**
- `lake build RoughBlocks.Heavy.Buchstab` → **OK**
- `lake build RoughBlocks.External.BridgeUniform` → **OK**
- `lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec` → **OK**

### ✅ Axioms (in `RoughBlocks/Light/Spec.lean`)
- **“Facade-only” mode** *(Spec **does not** import `Light.Existence` or the certificate)*:

Expect **only** the system ones: `propext`, `Classical.choice`, `Quot.sound`.
- **"Full integration" mode** *(Spec imports `Light.Existence` and `External.BridgeUniform`)*:

In addition to the system axioms, expect **exactly** these two external (reproducible) axioms:
- `RoughBlocks.Light.budget_verified_by_scan`
- `RoughBlocks.External.bridge_ge_1e6_uniform`

### ✅ (Optional) Smoke test
If the *scratch* executable exists:
```bash
lake exe roughblocks_scratch
```
Check access via (`RoughBlocks.Light.*`, `LB`, `margin`, `marginR`) and the theorem
(`main_theorem_ge_1e6`).

---

## Troubleshooting (FAQ)

**“no such file or directory … RoughBlocks/External/BridgeUniform.lean” (or similar module)**
You are on a case-sensitive FS (CI/Linux) or using an old build profile. Try:

```bash
# Correct capitalization of the import path:
# RoughBlocks/External/BridgeUniform.lean (not: external)

# Recommended local build (without running the 'scratch' demo):
chmod +x ./scripts/ci-local.sh
./scripts/ci-local.sh --no-scratch

# or minimal manual flow
lake update && lake exe cache get
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

**“unexpected token 'export'” / “unexpected token 'open'” in `RoughBlocks.lean`**
In Lean4, these commands do not re-export globally as you expect.
Keep **only** the `import` and use qualified names like `RoughBlocks.Light.*`.

**Aliases cause `dependsOnNoncomputable` / reducibility**
Avoid `def/abbrev` at the top pointing to `noncomputable` symbols from Light.
Prefer to use qualified names in clients: `RoughBlocks.Light.LB`, etc.

**Toolchain / cache divergence**
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
elan toolchain install "$(cat lean-toolchain)"
lake update && lake exe cache get
```

**Windows**
Use **WSL** or **Git Bash**:
```bash
bash ./scripts/ci-local.sh --no-scratch
```
---

## CI (GitHub Actions example)

```yaml
- name: Deps + cache
  run: lake update && lake exe cache get

- name: Make script executable
  run: chmod +x ./scripts/ci-local.sh

- name: Build (Light + Heavy, no scratch)
  run: ./scripts/ci-local.sh --no-scratch
```
In CI, it's common to **disable** the scratch step (`--no-scratch`) and **sync the toolchain/cache** before building.

---

## API stability policy

- The **Light** layer is the **official facade**.  
- Downstream users should **not** import `Heavy.*` directly.  
- `RoughBlocks.lean` (if present) stays minimal and only imports `Defs` + `Light.Export`.

---

## 🔒 Licenses

- **Code**: Apache License 2.0 — see [`LICENSE`](LICENSE) and [`NOTICE`](NOTICE).
- **Docs / papers / images**: CC BY-NC-ND 4.0 — see [`LICENSE-docs-CC-BY-NC-ND`](LICENSE-docs-CC-BY-NC-ND).

> Summary: code is open and collaboration-friendly (Apache-2.0); the scientific text and figures remain protected under CC BY-NC-ND.

> If you need permission for commercial use or derivative works, contact the authors.

---

## 📎 Quick reference

```bash
# (first time) make the script executable
chmod +x ./scripts/ci-local.sh

# Default run (Light + Heavy best-effort)
./scripts/ci-local.sh

# Light only
./scripts/ci-local.sh --light

# Heavy only (best-effort)
./scripts/ci-local.sh --heavy

# Skip downloading mathlib binary cache
./scripts/ci-local.sh --no-cache

# Do not run the demo executable (Scratch)
./scripts/ci-local.sh --no-scratch

# Reproducible manual flow (without the script)
lake update && lake exe cache get \
  && lake build RoughBlocks.Heavy.Numeric \
  && lake build RoughBlocks.Heavy.Buchstab \
  && lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```