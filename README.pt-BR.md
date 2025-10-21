# RoughBlocks — Lean 4
[![Lean CI](https://github.com/mariltondev/rough-blocks-lean/actions/workflows/ci.yml/badge.svg)](https://github.com/mariltondev/rough-blocks-lean/actions/workflows/ci.yml)
[![Release](https://img.shields.io/github/v/release/mariltondev/rough-blocks-lean.svg?label=release)](https://github.com/mariltondev/rough-blocks-lean/releases)
[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.17137291.svg)](https://doi.org/10.5281/zenodo.17137291)

> **Status:** versão pública estável `v1.0.0`
> **Toolchain:** `leanprover/lean4:v4.23.0` · **mathlib:** `v4.23.0` (fixado via `lean-toolchain`)

> **Idiomas:** Português (Brasil) · [English](README.md) · [Español](README.es-ES.md)

---

Este repositório contém a formalização completa em Lean 4 do teorema *RoughBlocks* sobre números $m$-ásperos próximos de $m^2$.  
Inclui o núcleo analítico (`Heavy`), a ponte certificada externa (`External`) e a interface pública estável (`Light`).

A **prioridade** é manter a camada **Light** estável e auditável, com provas em Lean
que dependem apenas dos axiomas “de sistema” (`propext`, `Classical.choice`, `Quot.sound`).

**Resultado principal:** para todo $m \ge 10^6$ e $x \le 8$,  
cada bloco $K_x = \{m^2 + xm + 1, \dots, m^2 + (x{+}1)m\}$  
contém pelo menos um número $m$-áspero ($P^-(n) > m$).

---

## Resumo
Mostramos que, para todo $m \ge 10^6$ e cada $x \in \{0,\dots,8\}$, o bloco
$K_x=\{m^2+xm+1,\dots,m^2+(x+1)m\}$ contém ao menos um número $m$-áspero
($P^-(n)>m$). A prova combina a identidade e a função de Buchstab $\omega$ com
a forma explícita de Mertens via soma de Abel, obtendo um lema local uniforme em  
intervalos curtos $[X,X+Y]$, com $X\in[y^2,y^3]$ e $y\le Y\le 2y$:

![Inequality](docs/img/formula01.svg)

$$
\bigl\lvert\,\{\,X<n\le X+Y:\ P^-(n)>y\,\}\,\bigr\rvert
\;\ge\; \frac{Y}{\log y}\,\omega\!\Bigl(\frac{\log X}{\log y}\Bigr)
\;-\; C_1\,\frac{Y}{\log^{2} y}\;-\; C_2.
$$

**Forma de ponte (caso dos blocos, usada no certificado):**  
Para $m\ge 10^6$ e $x\in\{0,\dots,8\}$:
$$
\bigl\lvert\,\{\,n\in K_x:\ P^-(n)>m\,\}\,\bigr\rvert \ \ge\ LB(m,x),
\qquad
LB(m,x)=\frac{m}{\log m}\,
\omega\!\Bigl(2+\frac{\log(1+x/m)}{\log m}\Bigr)
\;-\; C_1\,\frac{m}{\log^2 m}\;-\; C_2.
$$

Com constantes efetivas $C_0\le 2$, $C_1\le 4{,}4$ e $C_2=100$. Tratamos o bordo $X=y^2$
separadamente e eliminamos termos de fronteira pela convenção $\omega(u)=0$ em $0<u<1$.
Aplicando o lema local com $y=Y=m$ e $X=m^2+xm$, obtemos o resultado para cada $K_x$.

Com as constantes atuais, **cálculos numéricos sugerem** que o mesmo argumento já funcionaria a partir de
$m\ge 18,794$; contudo, neste repositório **certificamos formalmente**  $m\ge 10^6$ e cobrimos $2\le m<10^6$ por meio de uma varredura computacional **reprodutível** (código, logs e instruções em
[aqui](https://doi.org/10.5281/zenodo.17137291)).

### Integração com a formalização em Lean e certificados

- **Faixa finita $2 \le m < 10^6$:** encapsulada por um único axioma
  `RoughBlocks.Light.budget_verified_by_scan`, sustentado por varredura determinística
  (artefatos em [Zenodo — DOI: 10.5281/zenodo.17137291](https://doi.org/10.5281/zenodo.17137291)).

- **Faixa assintótica $m \ge 10^6$:** a “ponte” que compara o limite inferior analítico $LB(m,x)$
  com a contagem real no bloco $K_x$ é validada **uniformemente** por um certificado em Julia
  com aritmética intervalar (256 bits), armazenado em
  `certs/uniform-bridge-ge-1e6.json` e gerado por
  `external/julia/uniform_bridge_certificate.jl`. Esse certificado é importado em Lean pelo axioma
  `RoughBlocks.External.bridge_ge_1e6_uniform`.

---

## Introdução

Estudamos números $m$-ásperos (isto é, $P^-(n)>m$) em janelas curtas próximas de $m^2$. Este repositório isola o núcleo técnico que sustenta um programa mais amplo — doravante apelidado de “[`Conjectura de MariltonCR dos primos encaixados`](https://doi.org/10.5281/zenodo.16734582)”. O presente trabalho é inteiramente *incondicional*: provamos um resultado local uniforme que garante, para $m$ grande, a presença de um $m$-áspero em cada um de nove blocos consecutivos de comprimento $m$ imediatamente à direita de $m^2$.

Em trabalhos paralelos, desenvolvemos as implicações combinatórias e de crivo desse quadro para fechar algumas conjecturas clássicas: a **Hipótese de Legendre**, a **Conjectura de Oppermann**, a **Conjectura de Brocard** (na forma “$\ge 4$ primos entre $n^2$ e $(n{+}1)^2$”), a **Conjectura forte de Goldbach** (condicional às versões reforçadas do programa), bem como rederivar o **Postulado de Bertrand** como corolário. Em paralelo, abrimos uma linha de estudo conectando essas técnicas às heurísticas de crivo sob a **Hipótese de Riemann Generalizada (GRH)**.

Essas metas são deliberadamente ambiciosas: já as apresentamos como roteiro de pesquisa, e há ligações a este repositório. Aqui entregamos o primeiro tijolo técnico — um teorema local com constantes explícitas — sobre o qual as etapas seguintes estão sendo construídas em preprints separados, com evoluções periódicas.

## Mapeamento entre o artigo e a formalização em Lean

### Repositório do projeto (GitHub)
**Repo:** [`github.com/mariltondev/rough-blocks-lean`](https://github.com/mariltondev/rough-blocks-lean)

**PDF do artigo (para auditoria):** [`docs/primos_encaixados_acad.pdf`](docs/primos_encaixados_acad.pdf)

### Módulos atualmente no repositório
- `RoughBlocks/Defs.lean` — definições básicas: `mRough`, `K`, `BlockHasMRough`.
- `RoughBlocks/Heavy/Numeric.lean` — camada analítica usada pela Light:
  - `LB : ℕ → ℕ → ℝ`
  - `margin : ℕ → ℝ`
  - `marginR : ℝ → ℝ`
  - teorema `budget_conservative_formal`.
- `RoughBlocks/Heavy/Buchstab.lean` — **agregador** com identidades/contagens de Buchstab para `Φ`; lema `PhiGE_mono_in_X` (usado por `Light.Spec`).
- `RoughBlocks/External/BridgeUniform.lean` — axioma externo `bridge_ge_1e6_uniform` (importa o certificado JSON e expõe a ponte uniforme).
- `RoughBlocks/Light/Export.lean` — *facade* pública; reexporta a API comprovada e expõe `main_theorem_ge_1e6`.
- `RoughBlocks/Light/Spec.lean` — alvo de auditoria (`#print axioms`) e gancho para monotonicidade de `Φ`.
- `RoughBlocks/Check.lean` — (opcional) sanidade de API: exemplos de tipos e **lemas sentinela** que quebram se a superfície pública mudar.

## 🔧 Pré-requisitos

- `elan` (gerenciador de toolchains Lean) e `lake` no `PATH`.
- Git (para baixar a `mathlib` e seu cache).
- macOS/Linux com `bash`/`zsh` (Windows: WSL ou Git Bash).

**Dica (macOS):**
```bash
brew install elan-init
elan toolchain install v4.23.0
```

O arquivo `lean-toolchain` do projeto fixa a versão:  
```
leanprover/lean4:v4.23.0
```

---

## 🗂️ Estrutura do projeto (essencial)

```
RoughBlocks.lean                 # Ponto de entrada minimalista (importa Defs + Light.Export)
RoughBlocks/Defs.lean            # Definições básicas: mRough, K, BlockHasMRough

RoughBlocks/Heavy/Numeric.lean   # Núcleo numérico usado pela Light (sem axiomas externos)
RoughBlocks/Heavy/Buchstab.lean  # Identidades de Buchstab (discreto e em janela; agregador)

RoughBlocks/External/BridgeUniform.lean  # Importa o certificado JSON (ponte uniforme ≥ 1e6) para a Light

RoughBlocks/Light/Export.lean    # Facade pública: reexporta API formal comprovada
RoughBlocks/Light/Spec.lean      # Especificação/auditoria (hooks + #print axioms)

scripts/ci-local.sh              # CI-local (Light obrigatória + Heavy best-effort; flags --light/--heavy/--no-cache/--no-scratch)
AUDIT.md                         # Guia de auditoria
```

---

## 🚀 Uso rápido (build)

Atualize dependências e cache:
```bash
lake update && lake exe cache get
```

Compile **somente** o que existe no repositório atual:
```bash
# External (certificado uniforme ≥ 1e6)
lake build RoughBlocks.External.BridgeUniform

# Heavy (núcleo usado pela Light)
lake build RoughBlocks.Heavy.Numeric
lake build RoughBlocks.Heavy.Buchstab

# Light (facade + spec/auditoria)
lake build RoughBlocks.Light.Export RoughBlocks.Light.Spec

# Sanidade de API (arquivo sentinela; compila em silêncio)
lake build RoughBlocks.Check
```

Auditoria completa via script:
```bash
chmod +x scripts/ci-local.sh      # primeira vez
./scripts/ci-local.sh             # execução padrão (Light + Heavy best-effort)

# variações úteis:
./scripts/ci-local.sh --light
./scripts/ci-local.sh --heavy
./scripts/ci-local.sh --no-cache
./scripts/ci-local.sh --no-scratch
```

---

## 🧰 API pública (camada Light)

Importe a facade e use os nomes qualificados do namespace **Light**:

```lean
import RoughBlocks.Light.Export

-- Use nomes qualificados (recomendado):
#check RoughBlocks.Light.LB
#check RoughBlocks.Light.margin
#check RoughBlocks.Light.marginR
#check RoughBlocks.Light.budget_conservative_formal
#check RoughBlocks.Light.main_theorem_ge_1e6
```

**Teorema pronto** (exposto em `Light.Export`):

```lean
theorem RoughBlocks.Light.main_theorem_ge_1e6
  {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
  RoughBlocks.Light.LB m x ≥ 1
```

**Exemplo “sanity”** (compacto):

```lean
import RoughBlocks.Light.Export

example {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
    RoughBlocks.Light.LB m x ≥ 1 :=
  RoughBlocks.Light.main_theorem_ge_1e6 (m:=m) (x:=x) hm hx
```

> A Light **reexporta** símbolos provados em Heavy. Clientes **não** devem
> importar `RoughBlocks.Heavy.*` diretamente — preserve o encapsulamento.

---

## 🧪 Auditoria de axiomas

Abra `RoughBlocks/Light/Spec.lean` e rode no editor:

**Esperado (OK):** apenas `propext`, `Classical.choice`, `Quot.sound`.

Veja também o guia `AUDIT.md` e o script `scripts/ci-local.sh`.

---

## 📚 Módulos atualmente no repositório

- `RoughBlocks/Defs.lean` — definições básicas:  
  `mRough`, `K`, `BlockHasMRough`,  
  `roughSetInBlock`, `countRoughInBlock`,  
  lema existencial `exists_of_count_ge_one`.

- `RoughBlocks/Check.lean` — sanidade de API (exemplos-sentinela).
- `RoughBlocks/Scratch.lean` — executável de demonstração (alvo `roughblocks_scratch`).

- `RoughBlocks/Heavy/Buchstab/Core.lean` — primitivos combinatórios:  
  `isRoughGT`, `isRoughGE`, `PhiGT`, `PhiGE`, `primesIn`,  
  instâncias decidíveis e lemas básicos usados nas identidades.

- `RoughBlocks/Heavy/Buchstab/MinFac.lean` — camada fina sobre `Nat.minFac`:  
  lemas `minFac_prime_of_two_le`, `minFac_le_of_prime_dvd`, `minFac_dvd_eq`.

- `RoughBlocks/Heavy/Buchstab.lean` — **(opcional)** agregador que reexporta o núcleo de Buchstab.

- `RoughBlocks/Heavy/WindowLink/Core.lean` — “janela $ (N_1,N_2] \leftrightarrow $ diferença de $\Phi$”:
  `PhiGE_diff_window_eq`, `PhiGE_diff_window_ge`, `PhiGE_diff_window_ge_div`,  
  `sum_card_eq_sum_diff_phiGE`.

- `RoughBlocks/Heavy/WindowLink/Block.lean` — ponte bloco $\leftrightarrow$ janela (caso $p:=m{+}1$): 
  `countRoughInBlock_as_window`,  
  `strict_window_card_eq_phiDiff_succ` e versão em $\mathbb{R}$,
  `countRoughInBlock_eq_phiDiff_succ_real`.

- `RoughBlocks/Heavy/Identity.lean` — identidades de Buchstab (global e na janela):  
  `buchstab_identity_PhiGT`, `buchstab_identity_window_core`, `countWindow_as_sumDiff_real`,  
  versão com $1\le X$; equivalências `mRough`↔`isRoughGT` para $n\ge 1$; 
  `isRoughGT_iff_isRoughGE_succ_of_two_le`; monotonicidade `PhiGE_mono_in_X`.

- `RoughBlocks/Heavy/Numeric.lean` — camada analítica/conservativa **(sem axiomas externos)**:  
  `LB : ℕ → ℕ → ℝ`, `margin : ℕ → ℝ`, `marginR : ℝ → ℝ`,  
  lema `LB_ge_margin'`, marcos `margin_ge_one_at_1e6` e `margin_ge_one_from_1e6`,  
  teorema `budget_conservative_formal` ($m \ge 10^6$).

- **Módulos auxiliares (partes analíticas):**  
  `RoughBlocks/Heavy/Bridge.lean`  
  `RoughBlocks/Heavy/Interface.lean`  
  `RoughBlocks/Heavy/Log10Bounds.lean`  
  `RoughBlocks/Heavy/Omega.lean`

- `RoughBlocks/Light/Concrete.lean` — traduções concretas/auxiliares usadas no enunciado público.
- `RoughBlocks/Light/Existence.lean` — versão unificada do teorema de existência (camada Light);  
  **axioma externo** `budget_verified_by_scan` (faixa $2\le m<10^6,0\le x\le 8$).

- `RoughBlocks/Light/Export.lean` — *facade* pública; reexporta a API comprovada:  
  inclui o enunciado-alvo para uso externo, p.ex. `main_theorem_ge_1e6` e `budget_main`.

- `RoughBlocks/Light/Spec.lean` — alvo de auditoria (`#print axioms`);  
  consolida dependências externas visíveis na camada `Light`.

- `RoughBlocks/External/BridgeUniform.lean` — axioma externo `bridge_ge_1e6_uniform`;  
  importa o certificado Julia (JSON) e o expõe como ponte uniforme na formalização.

### Observação

Este projeto utiliza **duas dependências externas reprodutíveis**; todo o restante é provado internamente em Lean, usando apenas axiomas “de sistema” (`propext`, `Classical.choice`, `Quot.sound`).

- **Faixa finita $2 \le m < 10^6$.**  
  Encapsulada pelo axioma `RoughBlocks.Light.budget_verified_by_scan`
  (arquivo `RoughBlocks/Light/Existence.lean`), sustentado por varredura determinística
  (código, logs e instruções em [Zenodo — DOI: 10.5281/zenodo.17137291](https://doi.org/10.5281/zenodo.17137291)).  
  Em particular, para $2 \le m < 10^6$ e $0 \le x \le 8$, vale $\mathrm{LB}(m,x) \ge 1$.

- **Faixa assintótica $m \ge 10^6$.**  
  A “ponte” que compara o limite inferior analítico $LB(m,x)$ com a contagem real no bloco $K_x$
  é validada **uniformemente** via o axioma `RoughBlocks.External.bridge_ge_1e6_uniform`
  (arquivo `RoughBlocks/External/BridgeUniform.lean`), instanciado por um certificado em Julia com
  aritmética intervalar (256 bits), armazenado em `certs/uniform-bridge-ge-1e6.json`
  e gerado por `external/julia/uniform_bridge_certificate.jl`.

---

## Mapa Paper ↔ Lean (1×1)

| Conceito | LaTeX (esboço) | Lean (tipo) |
|---|---|---|
| "n é m-áspero (todo primo de n é > m)" | mRough(m,n) | `RoughBlocks.mRough m n : Prop` |
| Bloco K(m,x) | {m^2 + xm + 1, ..., m^2 + (x+1)m} | `RoughBlocks.K m x : Finset ℕ` |
| "K tem algum m-áspero" | ∃ n ∈ K(m,x): mRough(m,n) | `RoughBlocks.BlockHasMRough m x : Prop` |
| Limite inferior | LB(m,x) ≥ 1 (condições em m,x) | `RoughBlocks.Light.LB m x ≥ 1` *(reexportado em `Light.Export`)* |
| Monotonicidade (exemplo) | Φ_p(N1) ≤ Φ_p(N2) se N1 ≤ N2 | `PhiGE_mono_in_X p : Monotone (fun N => PhiGE N p)` |
| Buchstab (janela) | ∑_p (Φ((X+Y)/p) - Φ(X/p)) | ver lemas em `Heavy/Buchstab/Core` e `Heavy/WindowLink/Core` *(ver também `Heavy/Identity.lean`)* |

> Nota: a notação Lean usa `Nat`, `Finset` e `BigOperators` da `mathlib`.  
> As versões em `ℝ` surgem por coerção (`Nat.cast_*`) combinada com monotonicidade.

---

## 🧭 Política de estabilidade da API

- **Light** é a **fachada oficial** (*facade*, superfície pública estável).  
  - Garantimos **compatibilidade retroativa** dentro do mesmo *major* para nomes sob `RoughBlocks.Light.*`.
  - Quebras de API só ocorrem em **releases major** e serão documentadas em *release notes*.

- **Heavy** (`RoughBlocks.Heavy.*`) e **External** (`RoughBlocks.External.*`) são **detalhes internos**.  
  - Clientes **não devem** importá-los diretamente. Essas camadas podem mudar sem aviso.

- `RoughBlocks.lean` é **minimalista** (importa apenas `Defs` + `Light.Export`) e não adiciona API própria.  
  - Use sempre a facade: `import RoughBlocks.Light.Export`.

- `Light/Spec.lean` é **somente para auditoria** (`#print axioms`) e **não** faz parte da API pública.

- **Depreciações** na camada Light serão anunciadas com período de transição e caminhos de migração nas *release notes*.

---

## 🧩 Exemplos de uso (mínimos)

```lean
import RoughBlocks.Light.Export
import RoughBlocks.Defs

-- Use nomes curtos apenas da camada Light
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

## 🐛 Solução de problemas (FAQ)

- **Toolchain divergente / cache da mathlib**  
  ```bash
  cp .lake/packages/mathlib/lean-toolchain ./lean-toolchain
  elan toolchain install "$(cat lean-toolchain)"
  lake update && lake exe cache get
  ```

- **Erros ao tentar reexportar com `export`/`open (...)` no topo**  
  Mantenha o ponto de entrada simples (somente `import`); use os nomes qualificados
  `RoughBlocks.Light.*` em módulos clientes.

- **Aliases `abbrev/def` para itens `noncomputable`**  
  Evite “espelhar” os símbolos da Light no topo do `RoughBlocks` para não cair em
  `dependsOnNoncomputable`/reducibility. Use os nomes qualificados.

---

## 🔒 Licenças

- **Código**: Apache License 2.0 — veja [`LICENSE`](LICENSE) e [`NOTICE`](NOTICE).
- **Documentação / artigos / imagens**: CC BY-NC-ND 4.0 — veja [`LICENSE-docs-CC-BY-NC-ND`](LICENSE-docs-CC-BY-NC-ND.pt-BR).

> Resumo: o código é aberto e colaborativo (Apache-2.0); o texto científico e figuras ficam protegidos sob CC BY-NC-ND.

> Se você precisa de permissão para uso comercial ou obras derivadas, contate os autores.

---

### 🔎 Documentos de auditoria
- English: [`AUDIT.md`](AUDIT.md)
- Português (Brasil): [`AUDIT.pt-BR.md`](AUDIT.pt-BR.md)
- Español: [`AUDIT.es.md`](AUDIT.es.md)

---

## 🤝 Contribuindo

- Mantemos a **Light** estável; mudanças internas em **Heavy** devem preservar as assinaturas
  expostas por `Light.Export` (ou serem coordenadas com *release notes*).  
- Para novos módulos, adicione testes de auditoria em `Light/Spec.lean` quando fizer sentido.

---

## 🧪 CI (sugestão)

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