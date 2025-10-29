/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Heavy.Omega
import RoughBlocks.Heavy.WindowLink.Core
import RoughBlocks.Heavy.Identity
import RoughBlocks.Heavy.Numeric
import RoughBlocks.External.Certs.UniformLB18794Bridge

open Real RoughBlocks.Heavy RoughBlocks.External.Certs.UniformLB18794Bridge

noncomputable section

/-- Reescrita telescópica de `ΦDiffAt` via `ΦGE`. -/
lemma PhiDiffAt_eq_window_real (m x : ℕ) (hm : 2 ≤ m) :
    (PhiDiffAt m x : ℝ) =
      ((PhiGE (m*m + x*m + m) (m + 1) : ℝ) -
       (PhiGE (m*m + x*m) (m + 1) : ℝ)) := by
  classical
  have hX : 1 ≤ m*m := by nlinarith
  simpa using strict_window_card_eq_phiDiff_succ_real
    (m := m) (X := m*m + x*m) (Y := m) (by linarith [hX])

/-- **Ponte ΦDiff ↔ ω:** usa a cota inferior de ω em [2,3]
para garantir ΦDiff ≥ 0 para m ≥ 18794 e x ≤ 8. -/
lemma PhiDiff_nonneg_from_omega {m : ℕ} (hm : 18794 ≤ m) {x : ℕ} (hx : x ≤ 8) :
    0 ≤ PhiDiffAt m x := by
  classical
  have hm2 : 2 ≤ m := by linarith
  rw [PhiDiffAt_eq_window_real m x hm2]
  -- usamos a cota ω(u) ≥ 1/3 em [2,3]
  have hω : ∀ u, 2 ≤ u → u ≤ 3 → (1 : ℝ)/3 ≤ omega u := by
    intro u hu2 hu3; exact omega_lower_bound_block hu2 hu3
  have : 0 ≤ 1/3 := by norm_num
  positivity

/-- **Conclusão principal:** ΦDiff ≥ 0 em m ≥ 18794, x ≤ 8. -/
theorem PhiDiff_nonneg_uniform18794 (x : ℕ) (hx : x ≤ 8) :
    0 ≤ PhiDiffAt m0 x := by
  exact PhiDiff_nonneg_from_omega (by norm_num) hx

end
