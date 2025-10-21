/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic

noncomputable section
open Real

namespace RoughBlocks.Light

/-- Cota uniforme:
    para todo m ≥ 18793 e 0 ≤ x ≤ 8,
    log(m^2 + x m)/log m ≤ 2 + log(1 + 8/m)/log m. -/
lemma u_uniform_bound (m x : ℕ)
  (hm : 18793 ≤ m) (hx0 : 0 ≤ x) (hx8 : x ≤ 8) :
  (Real.log ((m:ℝ)^2 + (x:ℝ) * m)) / Real.log (m:ℝ)
    ≤ 2 + Real.log (1 + (8:ℝ) / m) / Real.log (m:ℝ) := by
  -- m ≥ 1 ⇒ m > 0 em ℝ
  have hm1 : 1 ≤ m := le_trans (by decide : 1 ≤ 18793) hm
  have hm_pos_nat : 0 < m := Nat.succ_le_iff.mp hm1
  have hm_pos : 0 < (m:ℝ) := by exact_mod_cast hm_pos_nat
  have hm_ne  : (m:ℝ) ≠ 0 := ne_of_gt hm_pos

  -- 0 ≤ x ≤ 8 em ℝ
  have hx0R : (0:ℝ) ≤ x := by exact_mod_cast hx0
  have hx8R : (x:ℝ) ≤ (8:ℝ) := by exact_mod_cast hx8

  -- Positividade dos argumentos de log
  have hsq_pos : 0 < (m:ℝ)^2 := by
    -- (m:ℝ)^2 = (m:ℝ) * (m:ℝ) > 0
    have := mul_pos hm_pos hm_pos
    simpa [pow_two] using this
  have hL_pos : 0 < (m:ℝ)^2 + (x:ℝ) * m :=
    add_pos_of_pos_of_nonneg hsq_pos (mul_nonneg hx0R (le_of_lt hm_pos))
  have hR_pos : 0 < (m:ℝ)^2 + (8:ℝ) * m :=
    add_pos_of_pos_of_nonneg hsq_pos (mul_nonneg (show (0:ℝ) ≤ 8 by norm_num) (le_of_lt hm_pos))

  -- Monotonicidade: x ≤ 8 ⇒ m^2 + x m ≤ m^2 + 8 m ⇒ log(...) ≤ log(...)
  have hAB :
      (m:ℝ)^2 + (x:ℝ) * m ≤ (m:ℝ)^2 + (8:ℝ) * m :=
    add_le_add_left
      (mul_le_mul_of_nonneg_right hx8R (le_of_lt hm_pos)) _
  have hlog_mono :
      Real.log ((m:ℝ)^2 + (x:ℝ) * m)
      ≤ Real.log ((m:ℝ)^2 + (8:ℝ) * m) :=
    (Real.log_le_log_iff hL_pos hR_pos).2 hAB

  -- Fatoração: m^2 + 8 m = m^2 * (1 + 8/m)
  have h_fact :
      (m:ℝ)^2 + (8:ℝ) * m = (m:ℝ)^2 * (1 + (8:ℝ) / m) := by
    -- (m^2)*(1 + 8/m) = m^2 + (m^2)*(8/m) = m^2 + 8m (pois m ≠ 0)
    have : (m:ℝ)^2 * ((8:ℝ) / m) = 8 * (m:ℝ) := by
      field_simp [hm_ne, pow_two]  -- transforma (m^2)*(8/m) em 8*m
    calc
      (m:ℝ)^2 + (8:ℝ) * m
          = (m:ℝ)^2 + (8 * (m:ℝ)) := by ring
      _   = (m:ℝ)^2 + (m:ℝ)^2 * ((8:ℝ) / m) := by simp [this]
      _   = (m:ℝ)^2 * (1 + (8:ℝ) / m) := by ring

  -- log do produto = soma dos logs (com hipóteses de positividade)
  have hpos_one_plus : 0 < (1 + (8:ℝ)/m) := by
    have : 0 < (8:ℝ)/m := div_pos (by norm_num) hm_pos
    linarith
  have h_log_right :
      Real.log ((m:ℝ)^2 + (8:ℝ) * m)
        = 2 * Real.log (m:ℝ) + Real.log (1 + (8:ℝ)/m) := by
    have hlog_mul₁ : Real.log ((m:ℝ)^2 * (1 + (8:ℝ)/m))
                      = Real.log ((m:ℝ)^2) + Real.log (1 + (8:ℝ)/m) :=
      Real.log_mul (ne_of_gt hsq_pos) (ne_of_gt hpos_one_plus)
    have hlog_pow : Real.log ((m:ℝ)^2) = 2 * Real.log (m:ℝ) := by
      -- log(m^2) = log(m*m) = log m + log m = 2*log m
      have := Real.log_mul (ne_of_gt hm_pos) (ne_of_gt hm_pos)
      simpa [pow_two, two_mul] using this
    calc
      Real.log ((m:ℝ)^2 + (8:ℝ) * m)
          = Real.log ((m:ℝ)^2 * (1 + (8:ℝ)/m)) := by simp [h_fact]
      _ = Real.log ((m:ℝ)^2) + Real.log (1 + (8:ℝ)/m) := by simp [hlog_mul₁]
      _ = 2 * Real.log (m:ℝ) + Real.log (1 + (8:ℝ)/m) := by simp [hlog_pow]

  -- log m > 0 pois m > 1
  have hm_gt_one : (1:ℝ) < (m:ℝ) := by
    have : (1:ℕ) < m := lt_of_lt_of_le (by decide : (1:ℕ) < 18793) hm
    exact_mod_cast this

  -- `Real.log_pos_iff` precisa primeiro de `0 ≤ m` para produzir o ↔
  have hlogm_pos : 0 < Real.log (m:ℝ) :=
    (Real.log_pos_iff (x := (m:ℝ)) (by exact hm_pos.le)).2 hm_gt_one
  have hlogm_nonneg : 0 ≤ Real.log (m:ℝ) := hlogm_pos.le
  have hden_ne : Real.log (m:ℝ) ≠ 0 := ne_of_gt hlogm_pos

  -- Dividindo a desigualdade por log m ≥ 0:
  have h_div :
      Real.log ((m:ℝ)^2 + (x:ℝ) * m) / Real.log (m:ℝ)
      ≤ Real.log ((m:ℝ)^2 + (8:ℝ) * m) / Real.log (m:ℝ) :=
    div_le_div_of_nonneg_right hlog_mono hlogm_nonneg

  -- RHS = 2 + log(1+8/m)/log m
  have h_rhs_simp :
      (2 * Real.log (m:ℝ) + Real.log (1 + (8:ℝ)/m)) / Real.log (m:ℝ)
        = 2 + Real.log (1 + (8:ℝ)/m) / Real.log (m:ℝ) := by
    -- (A+B)/L = A/L + B/L e (2*log m)/log m = 2
    have : (2 * Real.log (m:ℝ)) / Real.log (m:ℝ) = (2:ℝ) := by
      field_simp [hden_ne]
    calc
      (2 * Real.log (m:ℝ) + Real.log (1 + (8:ℝ)/m)) / Real.log (m:ℝ)
          = (2 * Real.log (m:ℝ)) / Real.log (m:ℝ)
            + Real.log (1 + (8:ℝ)/m) / Real.log (m:ℝ) := by
              simp [add_div]
      _   = 2 + Real.log (1 + (8:ℝ)/m) / Real.log (m:ℝ) := by simp [this]

  -- Conclusão
  have : Real.log ((m:ℝ)^2 + (8:ℝ) * m) / Real.log (m:ℝ)
          = 2 + Real.log (1 + (8:ℝ)/m) / Real.log (m:ℝ) := by
    simp [h_log_right, h_rhs_simp]
  -- Junta tudo
  simpa [this] using h_div

end RoughBlocks.Light
