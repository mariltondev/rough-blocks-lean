/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Lake
open Lake DSL

/-!
# Configuração Lake — RoughBlocks

Arquivo único de configuração de build e dependências.
Pensado para **reprodutibilidade** (CI) e simplicidade local.

* Não introduz opções específicas de compilação; os padrões do Lake
  são suficientes para uma biblioteca Lean pura.
* A dependência `mathlib` está **fixada** em um _tag_ para builds determinísticos.
  Para atualizar, ajuste o tag e rode `lake update`.
-/

package «rough-blocks-lean» where
  -- Metadados e opções do pacote (mantidos mínimos por design).

-- Dependências externas (fixadas para reprodutibilidade)
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.23.0"
/-!
Notas:
* O pin no `@ "v4.23.0"` garante que CI e desenvolvimento local
  usem a mesma versão de `mathlib`.
* Após alterar o tag, execute:
    - `lake update` para sincronizar as deps
    - (opcional) `lake exe cache get` se você usa o cache binário da mathlib
-/

@[default_target]
lean_lib RoughBlocks
/-!
O `default_target` permite compilar o projeto com `lake build`
e expõe `RoughBlocks` como a unidade principal para import por dependentes.
-/

-- Executável opcional de testes rápidos / auditoria leve
lean_exe roughblocks_scratch {
  root := `RoughBlocks.Scratch
  supportInterpreter := true
}
