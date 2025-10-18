/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.Bridge

/-!
# RoughBlocks.Light.Export

Camada **Light** (fachada): reexporta a API estável da camada **Heavy**
e fornece teoremas prontos para uso externo.

* **Escopo**: sem axiomas adicionais; apenas empacota e encadeia resultados já
  provados na Heavy.
* **Objetivo**: expor um ponto único e estável para usuários do projeto,
  sem que precisem conhecer detalhes internos das provas analíticas/combinatórias.
-/

namespace RoughBlocks.Light

/- Reexporta símbolos públicos da camada Heavy usados pelos usuários.

Inclui:
* `LB`, `margin`, `marginR` — funções analíticas/cotas.
* `budget_conservative_formal` — teorema formal para `m ≥ 10^6` e `x ≤ 8`.
-/
export RoughBlocks.Heavy.Numeric
  ( LB margin marginR
    budget_conservative_formal
  )

/-- Limite inferior formal.
Para `m ≥ 10⁶` e `x ≤ 8`, vale `LB m x ≥ 1`.
Uso: ponto de entrada direto na faixa formal, sem detalhes analíticos. -/
theorem main_theorem_ge_1e6 {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
  LB m x ≥ 1 :=
  budget_conservative_formal (m := m) (x := x) hm hx

/-- Existência no bloco, ramo `m ≥ 10⁶`.
Versão modular que assume apenas dois insumos:
1. `hCountEq`: identificação da contagem no bloco com um número real `D`;
2. `hD_ge_LB`: cota inferior analítica `D ≥ LB m x`.
Conclui `∃ n ∈ K m x, mRough m n` sem axiomas adicionais. -/
theorem exist_in_block_ge_1e6_of_local
  {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8)
  {D : ℝ}
  (hD_ge_LB : D ≥ LB m x)
  (hCountEq :
      (RoughBlocks.countRoughInBlock m x : ℝ) = D) :
  ∃ n ∈ RoughBlocks.K m x, RoughBlocks.mRough m n := by
  have hLB : (1 : ℝ) ≤ LB m x := main_theorem_ge_1e6 hm hx
  have hLB_le_D : (LB m x : ℝ) ≤ D := by simpa [ge_iff_le] using hD_ge_LB
  have hBridge : (LB m x : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ) := by
    simpa [hCountEq] using hLB_le_D
  have hCountℝ : (1 : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ) :=
    le_trans hLB hBridge
  have hCountℕ : 1 ≤ RoughBlocks.countRoughInBlock m x := by
    exact_mod_cast hCountℝ
  exact RoughBlocks.exists_of_count_ge_one hCountℕ

/-- Existência no bloco, ramo `m ≥ 10⁶`, sob a hipótese direta `LB ≤ contagem`.
Forma reduzida do teorema anterior: aplica o lema genérico
`exists_in_block_of_LB_ge_one` com a ponte `LB ≤ contagem`. -/
theorem exist_in_block_ge_1e6_if_bridge
  {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8)
  (hBridge : (LB m x : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ)) :
  ∃ n ∈ RoughBlocks.K m x, RoughBlocks.mRough m n := by
  have hLB : LB m x ≥ (1 : ℝ) := main_theorem_ge_1e6 hm hx
  exact RoughBlocks.Heavy.exists_in_block_of_LB_ge_one
    (LBf := fun m x => (LB m x : ℝ)) m x hLB
    (show (RoughBlocks.countRoughInBlock m x : ℝ) ≥ (LB m x : ℝ) from hBridge)

end RoughBlocks.Light
