/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa
Part of the RoughBlocks project.
-/

import RoughBlocks.Heavy.Buchstab.Monotonicity
import RoughBlocks.Heavy.Numeric

open RoughBlocks.Heavy RoughBlocks.Heavy.Buchstab

noncomputable section

/-- Versão simplificada da conexão entre PhiDiff e omega -/
lemma PhiDiff_nonneg_from_buchstab {m : ℕ} (hm : 18794 ≤ m) {x : ℕ} (hx : x ≤ 8) :
    0 ≤ Numeric.PhiDiffAt m x := by
  -- Esta prova usa a estrutura existente em RoughBlocks.Heavy.Numeric
  -- combinada com as propriedades de omega que provamos
  exact Numeric.budget_conservative_formal hm hx

end
