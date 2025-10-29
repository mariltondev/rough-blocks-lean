/-
SPDX-License-Identifier: Apache-2.0
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block

/-!
# Ponte 2 — de `LB` para `PhiDiffAt`

Objetivo: transformar uma desigualdade do tipo
`LB m x ≤ (countRoughInBlock m x : ℝ)`
na forma-alvo
`LB m x ≤ PhiDiffAt m x`,
usando a identidade de janela (caso `p := m+1`) já provada em `Block.lean`.

Apenas requer as hipóteses “curtas” padrão:
* `2 ≤ m` (para garantir `1 ≤ X` na janela),
* `x ≤ 8` (faixa dos 9 blocos).

Se você já tiver um lema que entregue `LB m x ≤ (countRoughInBlock m x : ℝ)`
para `m ≥ m₀`, basta combiná-lo com o teorema principal abaixo.
-/

namespace RoughBlocks.Heavy
open Real
open RoughBlocks.Heavy.Numeric

/-- Diferença telescópica de `PhiGE` correspondente ao bloco `K(m,x)` (caso `p := m+1`). -/
@[inline] def PhiDiffAt (m x : ℕ) : ℝ :=
  (PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ)

/-! ## Teorema principal da Ponte 2 -/

/-- **Ponte 2 (forma geral)**.
Se `LB m x ≤ (countRoughInBlock m x : ℝ)`, então `LB m x ≤ PhiDiffAt m x`.

As únicas hipóteses “curtas” adicionais são:
* `2 ≤ m` (usa-se para `1 ≤ X` na janela),
* `x ≤ 8` (estamos nos 9 blocos padrão).
-/
theorem LB_le_PhiDiff_of_LB_le_count
  {m x : ℕ} (hm2 : 2 ≤ m) (hx : x ≤ 8)
  (hLBcount : LB m x ≤ (RoughBlocks.countRoughInBlock m x : ℝ)) :
  LB m x ≤ PhiDiffAt m x := by
  -- identidade bloco ↔ diferença de PhiGE (em ℝ), já em `Block.lean`
  have hEq := countRoughInBlock_eq_phiDiff_succ_real m x hm2 hx
  -- substitui a contagem pelo `PhiDiffAt`
  simpa [PhiDiffAt, hEq] using hLBcount

/-- **Ponte 2 (forma “plug-and-play”)**.
Qualquer hipótese `hLBcount : LB m x ≤ (countRoughInBlock m x : ℝ)` + `2 ≤ m`, `x ≤ 8`
entrega `LB m x ≤ PhiDiffAt m x`.
-/
theorem LB_le_PhiDiff
  {m x : ℕ} (hm2 : 2 ≤ m) (hx : x ≤ 8)
  (hLBcount : LB m x ≤ (RoughBlocks.countRoughInBlock m x : ℝ)) :
  LB m x ≤ PhiDiffAt m x :=
  LB_le_PhiDiff_of_LB_le_count hm2 hx hLBcount

end RoughBlocks.Heavy
