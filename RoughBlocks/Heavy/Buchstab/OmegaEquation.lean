/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa
Part of the RoughBlocks project.
-/

import Mathlib
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import RoughBlocks.Heavy.Omega

open RoughBlocks.Heavy Real MeasureTheory intervalIntegral

noncomputable section

/-- Equação formal: `(u * ω(u)) = 1 + ∫₁^{u−1} (1/t) dt)` válida em `[2,3]`. -/
lemma omega_eq_integral_formal (u : ℝ) (h2 : 2 ≤ u) (h3 : u ≤ 3) :
    u * omega u = 1 + ∫ t in 1..(u - 1), 1 / t := by
  have hform : omega u = (1 + log (u - 1)) / u := by simp [omega, h3]
  rw [hform]; field_simp; ring_nf
  -- usamos o teorema fundamental do cálculo com log
  have h_deriv : ∀ x ∈ Set.Ioo 1 (u - 1), HasDerivAt log (1 / x) x := by
    intro x hx
    exact hasDerivAt_log (by linarith)
  have h_cont : ContinuousOn (fun x : ℝ ↦ 1 / x) (Set.Icc 1 (u - 1)) :=
    (continuousOn_inv₀ continuousOn_id).mono (Set.Icc_subset_Icc (by norm_num) (by linarith))
  have h_int := MeasureTheory.integral_eq_sub_of_hasDerivAt h_cont h_deriv
  rw [← h_int (by norm_num) (by linarith)]
  ring_nf

/-- Valor exato em `u = 2`: `ω(2) = 1/2`. -/
lemma omega_two_value : omega 2 = 1 / 2 := by simp [omega]

end
