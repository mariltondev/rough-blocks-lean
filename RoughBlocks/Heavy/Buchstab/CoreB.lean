/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa
Part of the RoughBlocks project.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace RoughBlocks.Heavy.Buchstab

open Real

/-- Função de Buchstab ω(u) - definição direta -/
noncomputable def omega (u : ℝ) : ℝ :=
  if u < 1 then 0
  else if u ≤ 2 then 1 / u
  else if u ≤ 3 then (1 + Real.log (u - 1)) / u
  else 0

/-- Valor em `u = 1`. -/
@[simp] lemma omega_one : omega 1 = 1 := by
  simp [omega]

/-- Em `[1,2]`, vale `ω(u) = 1/u`. -/
lemma omega_eq_one_div {u : ℝ} (h1 : 1 ≤ u) (h2 : u ≤ 2) : omega u = 1 / u := by
  unfold omega
  have : ¬ u < 1 := by linarith
  simp [this, h2]

/-- Em `(2,3]`, vale `ω(u) = (1 + log(u-1))/u`. -/
lemma omega_eq_log_form {u : ℝ} (h1 : 2 < u) (h2 : u ≤ 3) : omega u = (1 + Real.log (u - 1)) / u := by
  unfold omega
  have h1' : ¬ u < 1 := by linarith
  have h2' : ¬ u ≤ 2 := by linarith
  simp [h1', h2', h2]

/-- Para u < 1, ω(u) = 0. -/
lemma omega_zero_of_lt_one {u : ℝ} (h : u < 1) : omega u = 0 := by
  unfold omega
  simp [h]

/-- Para u > 3, ω(u) = 0. -/
lemma omega_zero_of_gt_three {u : ℝ} (h : u > 3) : omega u = 0 := by
  unfold omega
  have h1 : ¬ u < 1 := by linarith
  have h2 : ¬ u ≤ 2 := by linarith
  have h3 : ¬ u ≤ 3 := by linarith
  simp [h1, h2, h3]

end RoughBlocks.Heavy.Buchstab
