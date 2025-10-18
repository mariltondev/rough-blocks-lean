/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

/-
RoughBlocks/Check.lean — Sanidade de API

Este módulo é intencionalmente simples: ele compila em silêncio e serve como
“porteiro” da API pública exposta pela camada Light. Se as assinaturas mudarem
de forma incompatível, este arquivo deixará de compilar, sinalizando o problema
no CI/local.

Regras:
- Sem `#eval`/prints.
- Sem aliases que mudem reducibility (`abbrev/def` para nomes da Light).
- Apenas referências *qualificadas* a símbolos públicos.

Se quiser inspeções interativas (#check/#print), faça-as localmente em
`RoughBlocks/Light/Spec.lean` — aqui mantemos silêncio.
-/

import RoughBlocks.Defs
import RoughBlocks.Light.Export

namespace RoughBlocks.Check

/-!
## Sanidade: formas de tipos (sem ruído)

Estes `example`s não executam nada; eles apenas *inferem tipos*.
Se algum tipo mudar, o arquivo falha na compilação.
-/
noncomputable section

/-- `LB : ℕ → ℕ → ℝ` (limite inferior em função de `m` e `x`). -/
example : ℕ → ℕ → ℝ := RoughBlocks.Light.LB

/-- `margin : ℕ → ℝ` (margem numérica — **um** argumento natural). -/
example : ℕ → ℝ := RoughBlocks.Light.margin

/-- `marginR : ℝ → ℝ` (margem auxiliar em `ℝ`). -/
example : ℝ → ℝ := RoughBlocks.Light.marginR

/-- Definições básicas permanecem com as formas esperadas. -/
example : Prop := RoughBlocks.mRough 5 10
example : Finset ℕ := RoughBlocks.K 3 4
example : Prop := RoughBlocks.BlockHasMRough 3 4

end

/-!
## Sanidade: enunciado público principal

Wrapper fino que referencia o teorema “pronto”. Se o enunciado
mudar, este lemma quebra — sinalizando alteração na superfície pública.
-/
theorem main_ge_1e6_sanity {m x : ℕ}
    (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
    RoughBlocks.Light.LB m x ≥ 1 :=
  RoughBlocks.Light.main_theorem_ge_1e6 (m:=m) (x:=x) hm hx

end RoughBlocks.Check
