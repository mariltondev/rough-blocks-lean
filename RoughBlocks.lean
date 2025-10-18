/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import RoughBlocks.Defs
import RoughBlocks.Light.Export
-- Intencionalmente **não** importamos `RoughBlocks.Heavy.*` aqui:
-- a fachada Light já depende de Heavy e mantém o isolamento da API.

/-!
# RoughBlocks

Ponto de entrada **oficial** da biblioteca.

Este módulo atua como *facade* e NÃO introduz novas definições;
ele apenas disponibiliza, via import, a superfície pública estável
exposta por `RoughBlocks.Light`.

## Uso recomendado
- Para chamar a API: use `RoughBlocks.Light.LB`, `RoughBlocks.Light.margin`, etc.
  (ou faça `open RoughBlocks.Light` no arquivo cliente).
- As definições básicas (`mRough`, `K`, `BlockHasMRough`) já estão em `RoughBlocks`.

Essa abordagem evita aliases no topo (`RoughBlocks.LB`, …), reduz atritos com
`noncomputable`/reducibility e preserva o encapsulamento da camada Heavy.
-/
