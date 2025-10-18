# AUDIT.md — Auditoria local do RoughBlocks

> **Idiomas**: [English](AUDIT.md) • **Português (Brasil)** • [Español](AUDIT.es-ES.md)

Este guia padroniza **como auditar localmente** o repositório `rough-blocks-lean`.
Ele reflete **exatamente o estado atual do seu projeto** (camadas `Defs`,
`Check` e `Scratch` — quando presentes —, `External.*`, `Heavy.*` e `Light.*`) — sem citar módulos inexistentes.

> Plataformas-alvo: macOS/Linux com `bash`/`zsh`. No Windows, usar **WSL** ou **Git Bash**.

---

## ✅ Checklist rápido (TL;DR)

1) **Atualize dependências e cache**  
```bash
lake update && lake exe cache get
```

2) **Compile apenas o que existe no repositório**  
```bash
# Heavy (núcleo usado pela Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# Certificado/ponte (atenção à capitalização do caminho)
lake build RoughBlocks.External.BridgeUniform

# Light (facade + especificação/auditoria)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

> **Integração completa (opcional):** se o seu `Spec` importar a existência,
> inclua também:
> ```bash
> lake build RoughBlocks.Light.Existence
> ```

3) **Audite axiomas (no editor VS Code/Lean)**  
Abra `RoughBlocks/Light/Spec.lean` e rode:

**Esperado:**
- Se o `Spec` estiver em modo *facade-only*: apenas os de sistema  
  (`propext`, `Classical.choice`, `Quot.sound`).
- Se o `Spec` importar a integração completa: além dos de sistema, exatamente  
  `RoughBlocks.Light.budget_verified_by_scan` e  
  `RoughBlocks.External.bridge_ge_1e6_uniform`.

---

## Pré-requisitos

- **elan/Lean 4** instalados; `lake` deve estar no `PATH`.
- **Git** operacional (para baixar `mathlib` e o cache binário).
- **VS Code** com a extensão Lean4 (recomendado) para inspecionar axiomas.

### (Opcional) Sincronizar a toolchain com a `mathlib` baixada
Se notar divergência de versões:
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
elan toolchain install "$(cat lean-toolchain)"
```

---

## Uso rápido do script (recomendado)

O repositório traz um script de CI local em `scripts/ci-local.sh`.

```bash
chmod +x ./scripts/ci-local.sh      # primeira vez
./scripts/ci-local.sh               # execução padrão (Light + Heavy best-effort)
```

**O que ele faz:**
1. Garante a raiz do repositório e verifica `lake` no `PATH`.
2. (Opcional) baixa o cache binário da mathlib: `lake exe cache get` (tolerante a falhas).
3. **Light (obrigatório):** compila, na ordem sugerida:  
   `RoughBlocks.Defs`, `RoughBlocks.Check`, `RoughBlocks.External.BridgeUniform`,  
   `RoughBlocks.Light.Export`, `RoughBlocks.Light.Existence`,  
   `RoughBlocks.Light.Spec`, `RoughBlocks.Light.Concrete`.
4. (Opcional) executa a demo *scratch* se existir: `lake exe roughblocks_scratch`.
5. Procura por `sorry|admit` e **falha** o passo Light se encontrar algo.
6. **Heavy (best-effort):** tenta compilar `RoughBlocks.Heavy.*` (falhas **não** derrubam o script).

### Flags suportadas
- `--light` – só a camada Light.
- `--heavy` – só a camada Heavy (não recomendado).
- `--no-cache` – não roda `lake exe cache get`.
- `--no-scratch` – não tenta executar a demo *scratch*.

**Exemplos:**
```bash
./scripts/ci-local.sh --no-cache --no-scratch
./scripts/ci-local.sh --light
./scripts/ci-local.sh --heavy
```

**Códigos de saída:** `0` (sucesso), `2` (*flag* desconhecida); outros = falha do comando subjacente.  
O script usa `set -euo pipefail`; a parte **Heavy** é *best-effort* e não falha o processo.

---

## Execução manual (sem script)

Se preferir, execute os comandos diretamente:

```bash
# 1) deps + cache
lake update && lake exe cache get

# 2) Heavy (núcleo usado pela Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# 3) (opcional) Externo/certificado — útil para checar capitalização em CI
lake build RoughBlocks.External.BridgeUniform

# 4) Light (facade + spec)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

Depois, abra `RoughBlocks/Light/Spec.lean` no VS Code e rode `#print axioms`
nos símbolos de interesse (ex.: `main_theorem_ge_1e6`).

> Observação: `RoughBlocks.lean` (se presente) apenas importa `Defs` e `Light.Export`.
> Ele compila “junto” quando os módulos acima compilam; **não** há alvo separado.

---

## O que verificar ao final

### ✅ Build  *(em FS sensível a maiúsculas/minúsculas)*
- `lake build RoughBlocks.Heavy.Numeric` → **OK**  
- `lake build RoughBlocks.Heavy.Buchstab` → **OK**  
- `lake build RoughBlocks.External.BridgeUniform` → **OK**
- `lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec` → **OK**

### ✅ Axiomas (em `RoughBlocks/Light/Spec.lean`)
- **Modo “facade-only”** *(Spec **não** importa `Light.Existence` nem o certificado)*:  
  espere **apenas** os de sistema: `propext`, `Classical.choice`, `Quot.sound`.
- **Modo “integração completa”** *(Spec importa `Light.Existence` e `External.BridgeUniform`)*:  
  além dos de sistema, espere **exatamente** estes dois axiomas externos (reprodutíveis):
  - `RoughBlocks.Light.budget_verified_by_scan`
  - `RoughBlocks.External.bridge_ge_1e6_uniform`

### ✅ (Opcional) Smoke test
Se existir executável *scratch*:
```bash
lake exe roughblocks_scratch
```
Verifique acesso via (`RoughBlocks.Light.*`, `LB`, `margin`, `marginR`) e ao teorema
(`main_theorem_ge_1e6`).

---

## Solução de problemas (FAQ)

**“no such file or directory … RoughBlocks/External/BridgeUniform.lean” (ou módulo similar)**  
Você está num FS sensível a maiúsculas/minúsculas (CI/Linux) ou usando um perfil antigo de build.
Tente:

```bash
# capitalização correta do caminho de import:
#   RoughBlocks/External/BridgeUniform.lean  (não: external)

# build local recomendado (sem rodar a demo 'scratch'):
chmod +x ./scripts/ci-local.sh
./scripts/ci-local.sh --no-scratch

# ou fluxo manual mínimo
lake update && lake exe cache get
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```

**“unexpected token 'export'” / “unexpected token 'open'” em `RoughBlocks.lean`**  
No Lean4, esses comandos não reexportam globalmente como você espera.  
Mantenha **apenas** os `import` e use nomes qualificados `RoughBlocks.Light.*`.

**Aliases causam `dependsOnNoncomputable` / reducibility**  
Evite `def/abbrev` no topo apontando para símbolos `noncomputable` da Light.  
Prefira usar os nomes qualificados em clientes: `RoughBlocks.Light.LB`, etc.

**Divergência de toolchain / cache**  
```bash
cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
elan toolchain install "$(cat lean-toolchain)"
lake update && lake exe cache get
```

**Windows**  
Use **WSL** ou **Git Bash**:
```bash
bash ./scripts/ci-local.sh --no-scratch
```
---

## CI (exemplo GitHub Actions)

```yaml
- name: Deps + cache
  run: lake update && lake exe cache get

- name: Tornar script executável
  run: chmod +x ./scripts/ci-local.sh

- name: Build (Light + Heavy, sem scratch)
  run: ./scripts/ci-local.sh --no-scratch
```
Em CI, o comum é **desligar** o *scratch* (`--no-scratch`) e **sincronizar a toolchain/cache** antes de compilar.

---

## Política de estabilidade da API

- A camada **Light** é a **facade oficial**.  
- Clientes **não** devem importar `Heavy.*` diretamente.  
- `RoughBlocks.lean` (se presente) fica minimalista e só importa `Defs` + `Light.Export`.

---

## 🔒 Licenças

- **Código**: Apache License 2.0 — veja [`LICENSE`](LICENSE) e [`NOTICE`](NOTICE).
- **Documentação / artigos / imagens**: CC BY-NC-ND 4.0 — veja [`LICENSE-docs-CC-BY-NC-ND`](LICENSE-docs-CC-BY-NC-ND.pt-BR).

> Resumo: o código é aberto e colaborativo (Apache-2.0); o texto científico e figuras ficam protegidos sob CC BY-NC-ND.

> Se você precisa de permissão para uso comercial ou obras derivadas, contate os autores.

---

## 📎 Referência rápida

```bash
# (primeira vez) tornar o script executável
chmod +x ./scripts/ci-local.sh

# Execução padrão (Light + Heavy best-effort)
./scripts/ci-local.sh

# Somente Light
./scripts/ci-local.sh --light

# Somente Heavy (best-effort)
./scripts/ci-local.sh --heavy

# Sem baixar cache binário da mathlib
./scripts/ci-local.sh --no-cache

# Não rodar o executável de demonstração (Scratch)
./scripts/ci-local.sh --no-scratch

# Fluxo manual reproduzível (sem o script)
lake update && lake exe cache get \
  && lake build RoughBlocks.Heavy.Numeric \
  && lake build RoughBlocks.Heavy.Buchstab \
  && lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec
```
