/-
SPDX-License-Identifier: Apache-2.0
Part of the RoughBlocks project.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
--import Mathlib.Analysis.Calculus.Deriv.MeanValue
import RoughBlocks.Heavy.Buchstab.CoreB
import RoughBlocks.Heavy.Buchstab.Equation
import Mathlib.Analysis.Calculus.MeanValue
--import RoughBlocks.Heavy.Omega.lean

open Real Set MeasureTheory
open scoped Topology

open RoughBlocks.Heavy.Buchstab

namespace RoughBlocks.Heavy.Buchstab
noncomputable section

set_option maxHeartbeats 4000000
-- set_option diagnostics true

/-!
# Monotonicidade para a função de Buchstab em `[2,3]`

Usamos a equação integral provada em `Equation.lean` para deduzir
a forma fechada de `u * omega u` e, daí, a monotonicidade (e a estrita).
-/

/-- Em `2 ≤ u ≤ 3`, vale a forma fechada `u * omega u = 1 + log (u - 1)`. -/
lemma u_mul_omega_eq_one_add_log_sub_one
    {u : ℝ} (hu : 2 ≤ u) (hu3 : u ≤ 3) :
    u * omega u = 1 + Real.log (u - 1) := by
  -- Equação integral de Buchstab, já provada:
  have hEq := buchstab_integral_equation (u := u) hu hu3
  -- Em [1, u-1], temos ω = 1/t (pois u-1 ≤ 2)
  have h1le  : (1 : ℝ) ≤ u - 1 := by linarith
  have h_ule2 : u - 1 ≤ 2      := by linarith
  have h_on_Icc : ∀ t ∈ Icc (1 : ℝ) (u - 1), omega t = 1 / t := by
    intro t ht
    exact omega_eq_one_div ht.1 (le_trans ht.2 h_ule2)
  -- Troca o integrando por 1/t (trabalhando em `uIcc` → `Icc` via `uIcc_of_le`):
  have h_swap :
      ∫ t in (1 : ℝ)..(u - 1), omega t
        = ∫ t in (1 : ℝ)..(u - 1), 1 / t := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    have htIcc : t ∈ Icc (1 : ℝ) (u - 1) := by
      simpa [uIcc_of_le h1le] using ht
    simpa using h_on_Icc t htIcc
  -- ∫₁^{u-1} (1/t) = log(u-1)
  have h_log : ∫ t in (1 : ℝ)..(u - 1), 1 / t = Real.log (u - 1) := by
    simpa using integral_one_div_from_one (u := u - 1) (hu := h1le)
  -- Fecha a igualdade substituindo a integral por `log(u-1)`:
  exact hEq.trans (congrArg (fun s => 1 + s) (h_swap.trans h_log))

/-- `u ↦ u * omega u` é **monótona** em `[2,3]`. -/
lemma monotoneOn_u_mul_omega_Icc_two_three :
    MonotoneOn (fun u : ℝ => u * omega u) (Icc (2 : ℝ) 3) := by
  intro u hu v hv huv
  -- forma fechada em ambos:
  have hu_closed : u * omega u = 1 + Real.log (u - 1) :=
    u_mul_omega_eq_one_add_log_sub_one hu.1 hu.2
  have hv_closed : v * omega v = 1 + Real.log (v - 1) :=
    u_mul_omega_eq_one_add_log_sub_one hv.1 hv.2
  -- de u ≤ v vem u-1 ≤ v-1; e (u-1),(v-1) > 0:
  have hsub   : u - 1 ≤ v - 1 := sub_le_sub_right huv 1
  have hu_pos : 0 < u - 1 := by linarith [hu.1]
  have hv_pos : 0 < v - 1 := by linarith [hv.1]
  -- log(u-1) ≤ log(v-1) via caracterização por exp:
  have hlog : Real.log (u - 1) ≤ Real.log (v - 1) := by
    -- u-1 ≤ exp(log(v-1)) = v-1
    have : u - 1 ≤ Real.exp (Real.log (v - 1)) := by
      simpa [Real.exp_log hv_pos] using hsub
    exact (Real.log_le_iff_le_exp hu_pos).mpr this
  -- conclui:
  simpa [hu_closed, hv_closed, add_le_add_iff_right] using hlog

/-- `u ↦ u * omega u` é **estritamente crescente** em `[2,3]`. -/
lemma strictMonoOn_u_mul_omega_Icc_two_three :
    StrictMonoOn (fun u : ℝ => u * omega u) (Icc (2 : ℝ) 3) := by
  intro u hu v hv huv
  -- forma fechada
  have hu_closed : u * omega u = 1 + Real.log (u - 1) :=
    u_mul_omega_eq_one_add_log_sub_one hu.1 hu.2
  have hv_closed : v * omega v = 1 + Real.log (v - 1) :=
    u_mul_omega_eq_one_add_log_sub_one hv.1 hv.2
  -- u < v ⇒ u-1 < v-1; positivos:
  have hlt   : u - 1 < v - 1 := sub_lt_sub_right huv 1
  have hu_pos : 0 < u - 1 := by linarith [hu.1]
  have hv_pos : 0 < v - 1 := by linarith [hv.1]
  -- log(u-1) < log(v-1) via caracterização por exp:
  have hlog : Real.log (u - 1) < Real.log (v - 1) := by
    -- u-1 < exp(log(v-1)) = v-1
    have : u - 1 < Real.exp (Real.log (v - 1)) := by
      simpa [Real.exp_log hv_pos] using hlt
    exact (Real.log_lt_iff_lt_exp hu_pos).mpr this
  -- conclui:
  simpa [hu_closed, hv_closed, add_lt_add_iff_right] using hlog






lemma integral_one_div_minus_half {t : ℝ} (ht : 1 ≤ t) :
    ∫ x in (1:ℝ)..t, (1/x - 1/2) = Real.log t - (t - 1)/2 := by
  have hf : IntervalIntegrable (fun x => 1/x) volume 1 t := by
    have hsubset : Icc (1:ℝ) t ⊆ ({0} : Set ℝ)ᶜ := by
      intro x hx
      have hx_pos : 0 < x := by linarith [hx.1]
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      simpa [Set.mem_singleton_iff] using hx_ne
    have hcont := (continuousOn_inv₀ (G₀ := ℝ)).mono hsubset
    have hcont' : ContinuousOn (fun x : ℝ => 1 / x) (uIcc (1:ℝ) t) := by
      simpa [uIcc_of_le ht, one_div] using hcont
    exact hcont'.intervalIntegrable
  have hg : IntervalIntegrable (fun _ => (1:ℝ)/2) volume 1 t :=
    ContinuousOn.intervalIntegrable continuousOn_const
  have hlog := integral_one_div_from_one (u := t) ht
  have hconst :
      ∫ x in (1:ℝ)..t, (1:ℝ)/2 = (t - 1)/2 := by
    simp [intervalIntegral.integral_const, sub_eq_add_neg, div_eq_mul_inv]
  have hsplit :
      ∫ x in (1:ℝ)..t, 1 / x - 1 / 2
        = (∫ x in (1:ℝ)..t, 1 / x) - ∫ x in (1:ℝ)..t, (1:ℝ)/2 := by
    simpa using intervalIntegral.integral_sub hf hg
  calc
    ∫ x in (1:ℝ)..t, (1/x - 1/2)
        = (∫ x in (1:ℝ)..t, 1/x) - ∫ x in (1:ℝ)..t, (1:ℝ)/2 := by
          simpa [one_div] using hsplit
    _ = Real.log t - (t - 1)/2 := by
      rw [hlog, hconst]

/-- Em `u ∈ [2,3]`, vale `ω(u) ≥ 1/2`.
Prova via forma fechada `u*ω(u)=1+log(u-1)` e integral não-negativa. -/
lemma omega_ge_one_half_on_Icc_two_three
  {u : ℝ} (hu2 : (2:ℝ) ≤ u) (hu3 : u ≤ (3:ℝ)) :
  (1:ℝ)/2 ≤ omega u := by
  -- forma fechada já provada no projeto
  have hEq : u * omega u = 1 + Real.log (u - 1) :=
    u_mul_omega_eq_one_add_log_sub_one hu2 hu3
  have hu_pos : 0 < u := by linarith
  have hu_ne  : u ≠ 0 := ne_of_gt hu_pos

  -- ω(u) = (1 + log(u−1))/u
  have hω : omega u = (1 + Real.log (u - 1)) / u := by
    rw [← mul_div_cancel_left₀ (omega u) hu_ne]
    rw [hEq]

  -- t := u-1 ∈ [1,2]
  set t : ℝ := u - 1
  have ht1 : (1:ℝ) ≤ t := by linarith [hu2]
  -- AQUI ESTÁ A CORREÇÃO:
  have ht2 : t ≤ (2:ℝ) := by linarith [hu3]

  -- integrando não-negativo em [1,t]: 1/x - 1/2 ≥ 0
  have hpoint : ∀ x ∈ Icc (1:ℝ) t, 0 ≤ 1/x - (1:ℝ)/2 := by
    intro x hx
    have hx_pos : 0 < x := by linarith [hx.1]
    have hx_le_two : x ≤ (2:ℝ) := le_trans hx.2 ht2
    have : (1:ℝ)/2 ≤ 1 / x := by
      simpa using one_div_le_one_div_of_le hx_pos hx_le_two
    exact sub_nonneg.mpr this

  -- ∫(1→t) (1/x - 1/2) ≥ 0
  have hint_nonneg :
      0 ≤ ∫ x in (1:ℝ)..t, (1/x - (1:ℝ)/2) :=
    intervalIntegral.integral_nonneg (μ := volume) ht1 hpoint

  -- integrabilidade das partes
  have hf_int :
      IntervalIntegrable (fun x : ℝ => 1/x) volume (1:ℝ) t := by
    have hsubset : Icc (1:ℝ) t ⊆ ({0} : Set ℝ)ᶜ := by
      intro x hx
      have hx_pos : 0 < x := by linarith [hx.1]
      show x ≠ (0 : ℝ)
      exact ne_of_gt hx_pos
    have hcont := (continuousOn_inv₀ (G₀ := ℝ)).mono hsubset
    have hcont' :
        ContinuousOn (fun x : ℝ => x⁻¹) (uIcc (1:ℝ) t) := by
      simpa [uIcc_of_le ht1] using hcont
    simpa [one_div] using hcont'.intervalIntegrable
  have hg_int :
      IntervalIntegrable (fun _ : ℝ => (1:ℝ)/2) volume (1:ℝ) t := by
    have hconst :
        ContinuousOn (fun _ : ℝ => (1:ℝ)/2) (uIcc (1:ℝ) t) :=
      continuousOn_const
    simpa using hconst.intervalIntegrable

  -- avalia integral: = log t − (t−1)/2
  have hint_value := integral_one_div_minus_half ht1

  -- (t−1)/2 ≤ log t
  have hlog_ge : (t - 1)/2 ≤ Real.log t := by
    have hnonneg : 0 ≤ Real.log t - (t - 1)/2 := by
      rw [hint_value] at hint_nonneg
      exact hint_nonneg
    exact sub_nonneg.mp hnonneg

  -- então u/2 ≤ 1 + log t
  have hnum : u/2 ≤ 1 + Real.log t := by
    have h := add_le_add_left hlog_ge (1:ℝ)
    have h' : (t + 1) / 2 ≤ 1 + Real.log t := by
      have hleft : 1 + (t - 1) / 2 = (t + 1) / 2 := by ring
      simpa [hleft] using h
    simpa [t] using h'

  -- volta para ω(u)
  have hfrac : (1:ℝ)/2 ≤ (1 + Real.log t) / u := by
    have := mul_le_mul_of_nonneg_right hnum (inv_nonneg.mpr hu_pos.le)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, t, hu_ne] using this

  simpa [hω, t] using hfrac




end
end RoughBlocks.Heavy.Buchstab
