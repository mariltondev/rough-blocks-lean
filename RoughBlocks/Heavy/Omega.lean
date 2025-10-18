/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib

/-!
# RoughBlocks.Heavy.Omega

Definição e propriedades elementares da função de Buchstab `ω(u)` nas faixas usadas.

Intervalos:
* `u ≤ 1`      → `ω(u) = 0`
* `1 < u ≤ 2`  → `ω(u) = 1 / u`
* `2 < u ≤ 3`  → `ω(u) = (1 + log(u − 1)) / u`

Resultados:
* `omega_at_2` : `ω(2) = 1/2`
* `omega_lower_bound_block` : `1/3 ≤ ω(u)` para `2 ≤ u ≤ 3`
* `omega_lower_23_fine` : `ω(u) ≥ 1/2 − (u − 2)/4` para `2 ≤ u ≤ 3`
-/

namespace RoughBlocks.Heavy
open scoped Real

/-- Função de Buchstab `ω(u)` nas faixas de interesse (definição por partes). -/
noncomputable def omega (u : ℝ) : ℝ :=
  if u ≤ 1 then 0
  else if u ≤ 2 then 1 / u
  else if u ≤ 3 then (1 + Real.log (u - 1)) / u
  else 0

/-- Valor exato em `u = 2`. -/
lemma omega_at_2 : omega 2 = 1 / 2 := by
  simp [omega]

/-- Cota inferior `1/3 ≤ ω(u)` para `2 ≤ u ≤ 3`. -/
lemma omega_lower_bound_block {u : ℝ} (h2 : 2 ≤ u) (h3 : u ≤ 3) :
    (1 : ℝ) / 3 ≤ omega u := by
  classical
  have h1 : ¬ u ≤ 1 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact not_le.mpr (lt_of_lt_of_le this h2)
  by_cases hu2 : u ≤ 2
  · have hu : u = 2 := le_antisymm hu2 h2
    subst hu
    have : (1 : ℝ) / 3 ≤ (1 : ℝ) / 2 := by norm_num
    simpa [omega] using this
  ·
    have hpos : 0 < u := by linarith
    have hlog_nonneg : 0 ≤ Real.log (u - 1) := by
      have : Real.log 1 ≤ Real.log (u - 1) :=
        Real.log_le_log (by norm_num) (by linarith : (1 : ℝ) ≤ u - 1)
      simpa [Real.log_one] using this
    have h13_le_1_over_u : (1 : ℝ) / 3 ≤ 1 / u := by
      have := one_div_le_one_div_of_le hpos h3
      simpa [one_div] using this
    have hnum_ge : (1 : ℝ) ≤ 1 + Real.log (u - 1) := by linarith [hlog_nonneg]
    have hfrac : 1 / u ≤ (1 + Real.log (u - 1)) / u :=
      div_le_div_of_nonneg_right hnum_ge hpos.le
    have hfinal : (1 : ℝ) / 3 ≤ (1 + Real.log (u - 1)) / u :=
      le_trans h13_le_1_over_u hfrac
    simpa [omega, h1, hu2, h3] using hfinal

/-- Cota `ω(u) ≥ 1/2 − (u − 2)/4` para `2 ≤ u ≤ 3`. -/
lemma omega_lower_23_fine {u : ℝ} (h2 : 2 ≤ u) (h3 : u ≤ 3) :
  omega u ≥ 1 / 2 - (u - 2) / 4 := by
  classical
  have h1 : ¬ u ≤ 1 := by
    have : (1 : ℝ) < 2 := by norm_num
    exact not_le.mpr (lt_of_lt_of_le this h2)
  by_cases hu2 : u ≤ 2
  ·
    have hu : u = 2 := le_antisymm hu2 h2
    subst hu; simp [omega]
  ·
    have hposu : 0 < u := by linarith
    have hδ0 : 0 ≤ u - 2 := by linarith
    have hlog_nonneg : 0 ≤ Real.log (1 + (u - 2)) := by
      have : Real.log 1 ≤ Real.log (1 + (u - 2)) :=
        Real.log_le_log (by norm_num) (by linarith : (1 : ℝ) ≤ 1 + (u - 2))
      simpa [Real.log_one] using this
    have hnum : 1 - (u - 2)^2 / 4 ≤ 1 + Real.log (1 + (u - 2)) := by
      have hq : - (u - 2)^2 / 4 ≤ 0 := by
        have : 0 ≤ (u - 2)^2 := by nlinarith
        linarith
      have : 1 ≤ 1 + Real.log (1 + (u - 2)) := by linarith [hlog_nonneg]
      exact le_trans (by linarith [hq]) this
    have hdiv : (1 - (u - 2)^2 / 4) / u ≤ (1 + Real.log (1 + (u - 2))) / u :=
      div_le_div_of_nonneg_right hnum hposu.le
    have hu_eq : u = 2 + (u - 2) := by ring
    have hdiv2 :
        (1 - (u - 2)^2 / 4) / (2 + (u - 2))
          ≤ (1 + Real.log (1 + (u - 2))) / (2 + (u - 2)) := by
      have : (0 : ℝ) ≤ 2 + (u - 2) := by linarith [hδ0]
      exact div_le_div_of_nonneg_right hnum this
    have hcancel :
        (1 - (u - 2)^2 / 4) / (2 + (u - 2))
          = (1 : ℝ) / 2 - (u - 2) / 4 := by
      have hfac : (4 - (u - 2)^2) = (2 - (u - 2)) * (2 + (u - 2)) := by ring
      have hstep :
          ((2 - (u - 2)) * (2 + (u - 2))) / (4 * (2 + (u - 2)))
            = (2 - (u - 2)) / 4 := by
        have hu' : u ≠ 0 := ne_of_gt hposu
        have hsum : 2 + (u - 2) = u := by ring
        field_simp [hsum, hu', mul_comm, mul_left_comm, mul_assoc]
      calc
        (1 - (u - 2)^2 / 4) / (2 + (u - 2))
            = ((4 - (u - 2)^2) / 4) / (2 + (u - 2)) := by ring
        _ = (4 - (u - 2)^2) / (4 * (2 + (u - 2))) := by
              simp [div_eq_mul_inv, mul_comm, mul_left_comm]
        _ = ((2 - (u - 2)) * (2 + (u - 2))) / (4 * (2 + (u - 2))) := by
              simp [hfac]
        _ = (2 - (u - 2)) / 4 := by simpa using hstep
        _ = (1 : ℝ) / 2 - (u - 2) / 4 := by ring
    have hω : omega u = (1 + Real.log (u - 1)) / u := by
      simp [omega, h1, hu2, h3]
    have : (1 - (u - 2)^2 / 4) / (2 + (u - 2)) ≤ (1 + Real.log (1 + (u - 2))) / (2 + (u - 2)) := by
      exact hdiv2
    have hrewrite1 : 1 + (u - 2) = u - 1 := by ring
    have hrewrite2 : 2 + (u - 2) = u := by ring
    have hineq1 : (1 : ℝ) / 2 - (u - 2) / 4 ≤ (1 + Real.log (1 + (u - 2))) / (2 + (u - 2)) := by
      calc
        (1 : ℝ) / 2 - (u - 2) / 4
          = (1 - (u - 2)^2 / 4) / (2 + (u - 2)) := by rw [hcancel.symm]
        _ ≤ (1 + Real.log (1 + (u - 2))) / (2 + (u - 2)) := hdiv2
    have : (1 : ℝ) / 2 - (u - 2) / 4 ≤ (1 + Real.log (u - 1)) / u := by
      simpa [hrewrite1, hrewrite2] using hineq1
    have : (1 : ℝ) / 2 - (u - 2) / 4 ≤ omega u := by
      simpa [hω] using this
    simpa using this

end RoughBlocks.Heavy
