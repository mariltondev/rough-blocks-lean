/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Bridge
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.Heavy.Log10Bounds
import RoughBlocks.External.Certs.FullVerifier

import RoughBlocks.External.Certs.Parte01         -- two_le_m0, uniformLB18794_gt_one, etc.
import RoughBlocks.External.Certs.Parte02         -- LB, margin, u∈[2,3], LB_ge_margin'
import RoughBlocks.External.Certs.Parte03         -- UniformBridgeFrom_m0, H_uniformBridgeFrom_m0
import RoughBlocks.External.Certs.Parte04

namespace RoughBlocks.External.Certs
noncomputable section
open Real
open Classical
open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.Heavy.Numeric
open RoughBlocks.External.Certs
open RoughBlocks.External.Certs.UniformLB18794Bridge
open RoughBlocks.External.Certs.UniformGE18794Bridge

-- Aliases (defeq) para reduzir ruído nos enunciados
abbrev vL       := RoughBlocks.External.Certs.UniformLB18794Bridge.vL
abbrev C1_q     := RoughBlocks.External.Certs.UniformLB18794Bridge.C1_q
abbrev omegaLo_q (x : Fin 9) : ℚ := RoughBlocks.External.Certs.UniformLB18794Bridge.omegaLo_q x

/-- Diferença `Φ` no bloco `x`, no nível `m`. -/
@[inline] def PhiDiffAt (m : ℕ) (x : ℕ) : ℝ :=
  (PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ)

/-- Parte principal do `LB` “congelado” (com `ω_lo`) como função de `L = log m`. -/
@[simp] def fL (x : Fin 9) (L : ℝ) : ℝ :=
  (omegaLo_q x : ℝ) * (L - vL x)^2  +  (2*(C1_q : ℝ) - (omegaLo_q x : ℝ) * (vL x)^2)

/-! ## 0. Lema auxiliar: BridgeThreshold ≤ m0 (versão com `decide`, já existente) -/

/-- **Computacional**: `BridgeThreshold ≤ m0`. -/
lemma bridgeThreshold_le_m0 : BridgeThreshold ≤ m0 := by
  decide

/-! ## 1. Monotonicidades elementares -/

/-- Monotonicidade de `log` a partir de `m0` (versão em `ℕ`). -/
lemma log_mono_from_m0_nat {m : ℕ} (hm : m0 ≤ m) :
    Real.log (m0 : ℝ) ≤ Real.log (m : ℝ) := by
  have hm0posℝ : 0 < (m0 : ℝ) := by exact_mod_cast (by decide : 0 < m0)
  have hle : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact Real.log_le_log hm0posℝ hle

/-- Se `ω ≥ 0`, `v ≤ L₁ ≤ L₂` então `ω*(L₁−v)^2 ≤ ω*(L₂−v)^2`. -/
lemma mono_sq_shift (ω v L₁ L₂ : ℝ)
    (hω : 0 ≤ ω) (hv : v ≤ L₁) (hL : L₁ ≤ L₂) :
  ω * (L₁ - v)^2 ≤ ω * (L₂ - v)^2 := by
  have h1 : 0 ≤ L₁ - v := sub_nonneg.mpr hv
  have h2 : 0 ≤ L₂ - v := sub_nonneg.mpr (le_trans hv hL)
  have hdiff : L₁ - v ≤ L₂ - v := sub_le_sub_right hL v
  have habs : |L₁ - v| ≤ |L₂ - v| := by
    simpa [abs_of_nonneg h1, abs_of_nonneg h2] using hdiff
  have hsq : (L₁ - v)^2 ≤ (L₂ - v)^2 := by
    simpa [pow_two] using (sq_le_sq.mpr habs)
  exact mul_le_mul_of_nonneg_left hsq hω

/-- Versão direta para `L = log m` usando `m ≥ m0`. -/
lemma mono_main_from_m0_nat_of_cert
    (ω v : ℝ) {m : ℕ}
    (hm : m0 ≤ m) (hω : 0 ≤ ω) (hv : v ≤ Real.log (m0 : ℝ)) :
  ω * (Real.log (m0 : ℝ) - v)^2 ≤ ω * (Real.log (m : ℝ) - v)^2 := by
  have hlog : Real.log (m0 : ℝ) ≤ Real.log (m : ℝ) := log_mono_from_m0_nat hm
  exact mono_sq_shift ω v (Real.log (m0 : ℝ)) (Real.log (m : ℝ)) hω
    (by simpa using hv) hlog

/-- Monotonicidade de `fL` em `L = log m` quando `vL ≤ log m0 ≤ log m`. -/
lemma fL_mono_from_m0 (x : Fin 9) {m : ℕ}
    (hm : m0 ≤ m) (hv : vL x ≤ Real.log (m0 : ℝ)) :
    fL x (Real.log (m0 : ℝ)) ≤ fL x (Real.log (m : ℝ)) := by
  have hω : 0 ≤ (omegaLo_q x : ℝ) := (omegaLo_pos x).le
  have hmain :
      (omegaLo_q x : ℝ) * (Real.log (m0 : ℝ) - vL x)^2
        ≤ (omegaLo_q x : ℝ) * (Real.log (m : ℝ) - vL x)^2 :=
    mono_main_from_m0_nat_of_cert (ω := (omegaLo_q x : ℝ)) (v := vL x) hm hω hv
  have hconst :
      (2*(C1_q : ℝ) - (omegaLo_q x : ℝ) * (vL x)^2)
      ≤ (2*(C1_q : ℝ) - (omegaLo_q x : ℝ) * (vL x)^2) := le_rfl
  simpa [fL] using add_le_add hmain hconst

/-- Forma nomeada do lema anterior. -/
theorem LB_from_cert_monotone_ge_m0 (x : Fin 9) {m : ℕ}
    (hm : m0 ≤ m) (hv : vL x ≤ Real.log (m0 : ℝ)) :
  fL x (Real.log (m0 : ℝ)) ≤ fL x (Real.log (m : ℝ)) :=
  fL_mono_from_m0 x hm hv

/-- Monotonicidade de `fL` para `L ≥ vL`. -/
lemma fL_mono_in_L_right_of_v (x : Fin 9) {L : ℝ}
    (hv : vL x ≤ L) :
  fL x (vL x) ≤ fL x L := by
  have hω : 0 ≤ (omegaLo_q x : ℝ) := (omegaLo_pos x).le
  have hmain :
      (omegaLo_q x : ℝ) * (vL x - vL x)^2
        ≤ (omegaLo_q x : ℝ) * (L - vL x)^2 :=
    mono_sq_shift (ω := (omegaLo_q x : ℝ)) (v := vL x)
      (L₁ := vL x) (L₂ := L) hω (by exact le_rfl) hv
  have hconst :
      (2*(C1_q : ℝ) - (omegaLo_q x : ℝ) * (vL x)^2)
      ≤ (2*(C1_q : ℝ) - (omegaLo_q x : ℝ) * (vL x)^2) := le_rfl
  simpa [fL, sub_self] using add_le_add hmain hconst

/-! ## 2. Bounds `vL ≤ log m0` (original + versão parametrizada) -/

/-- `4·log 10 ≤ log m0` (forma concreta; usa `native_decide` para `10000 ≤ m0`). -/
lemma four_log10_le_log_m0 : (4:ℝ) * Real.log (10:ℝ) ≤ Real.log (m0 : ℝ) := by
  have : (10000 : ℕ) ≤ m0 := by native_decide
  have : (10000 : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast this
  calc
    (4:ℝ) * Real.log (10:ℝ) = Real.log ((10:ℝ)^4) := by
      have h10pos : (0:ℝ) < 10 := by norm_num
      simpa using (Real.log_pow h10pos 4)
    _ = Real.log (10000 : ℝ) := by norm_num
    _ ≤ Real.log (m0 : ℝ) := Real.log_le_log (by norm_num) this

/-- **Parametrizada**: se `10000 ≤ m0`, então `4·log 10 ≤ log m0`. -/
lemma four_log10_le_log_m0_of_10000_le (h10000 : (10000 : ℕ) ≤ m0) :
    (4:ℝ) * Real.log (10:ℝ) ≤ Real.log (m0 : ℝ) := by
  have : (10000 : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast h10000
  calc
    (4:ℝ) * Real.log (10:ℝ) = Real.log ((10:ℝ)^4) := by
      have h10pos : (0:ℝ) < 10 := by norm_num
      simpa using (Real.log_pow h10pos 4)
    _ = Real.log (10000 : ℝ) := by norm_num
    _ ≤ Real.log (m0 : ℝ) := Real.log_le_log (by norm_num) this

/-- `5 ≤ log m0` via `46/5 = 4·(23/10) ≤ 4·log 10 ≤ log m0`. -/
lemma five_le_log_m0 : (5:ℝ) ≤ Real.log (m0 : ℝ) := by
  have hlog10 : (23:ℝ)/10 ≤ Real.log (10:ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr (RoughBlocks.Heavy.Log10Bounds.exp_23_tenths_le_10)
  have h92_le_4log10 : (46:ℝ)/5 ≤ 4 * Real.log (10:ℝ) := by
    have : (46:ℝ)/5 = 4 * ((23:ℝ)/10) := by norm_num
    simpa [this] using mul_le_mul_of_nonneg_left hlog10 (by norm_num : (0:ℝ) ≤ 4)
  have h4log10_le := four_log10_le_log_m0
  have h92_le : (46:ℝ)/5 ≤ Real.log (m0 : ℝ) := h92_le_4log10.trans h4log10_le
  have : (5:ℝ) ≤ (46:ℝ)/5 := by norm_num
  exact this.trans h92_le

/-- **Parametrizada**: se `10000 ≤ m0`, então `5 ≤ log m0`. -/
lemma five_le_log_m0_of_10000_le (h10000 : (10000 : ℕ) ≤ m0) :
  (5:ℝ) ≤ Real.log (m0 : ℝ) := by
  have hlog10 : (23:ℝ)/10 ≤ Real.log (10:ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num)).mpr (RoughBlocks.Heavy.Log10Bounds.exp_23_tenths_le_10)
  have h92_le_4log10 : (46:ℝ)/5 ≤ 4 * Real.log (10:ℝ) := by
    have : (46:ℝ)/5 = 4 * ((23:ℝ)/10) := by norm_num
    simpa [this] using mul_le_mul_of_nonneg_left hlog10 (by norm_num : (0:ℝ) ≤ 4)
  have h4log10_le := four_log10_le_log_m0_of_10000_le h10000
  have h92_le : (46:ℝ)/5 ≤ Real.log (m0 : ℝ) := h92_le_4log10.trans h4log10_le
  have : (5:ℝ) ≤ (46:ℝ)/5 := by norm_num
  exact this.trans h92_le

/-- De `vL ≤ 5` obtemos `vL ≤ log m0`. -/
lemma vL_le_logm0_of_bound (x : Fin 9) (hvl5 : vL x ≤ (5:ℝ)) :
  vL x ≤ Real.log (m0 : ℝ) :=
  hvl5.trans five_le_log_m0

/-- **Parametrizada**: de `vL ≤ 5` e `10000 ≤ m0` obtemos `vL ≤ log m0`. -/
lemma vL_le_logm0_of_bound_of_10000_le (x : Fin 9)
  (hvl5 : vL x ≤ (5:ℝ)) (h10000 : (10000 : ℕ) ≤ m0) :
  vL x ≤ Real.log (m0 : ℝ) :=
  hvl5.trans (five_le_log_m0_of_10000_le h10000)

/-! ## 3. Ponte via margem (faixa formal `m ≥ BridgeThreshold`) -/

/-- Versão original (usa `by decide` para `U0Default ≤ BridgeThreshold`). -/
lemma fL_le_PhiDiff
  {m : ℕ} (hm : BridgeThreshold ≤ m) (x : Fin 9)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  fL x (Real.log (m : ℝ)) ≤ PhiDiffAt m (x : ℕ) := by
  have hx  : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  have hmU : U0Default ≤ m := (le_trans (by decide : U0Default ≤ BridgeThreshold) hm)
  have h_margin_le_LB :
      RoughBlocks.Heavy.Numeric.margin m
        ≤ RoughBlocks.Heavy.Numeric.LB m (x : ℕ) :=
    RoughBlocks.Heavy.Numeric.LB_ge_margin' (m := m) (x := (x : ℕ)) hmU hx
  exact le_trans h_fL_le_margin (le_trans h_margin_le_LB h_LB_le_PhiDiff)

/-- **Parametrizada**: se `U0Default ≤ BridgeThreshold` e `BridgeThreshold ≤ m`,
então `fL(log m) ≤ Φ-dif(m,x)` assumindo `fL ≤ margin` e `LB ≤ Φ-dif`. -/
lemma fL_le_PhiDiff_of_hU0B
  {m : ℕ} (hU0B : U0Default ≤ BridgeThreshold) (hm : BridgeThreshold ≤ m) (x : Fin 9)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  fL x (Real.log (m : ℝ)) ≤ PhiDiffAt m (x : ℕ) := by
  have hx  : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  have hmU : U0Default ≤ m := (le_trans hU0B hm)
  have h_margin_le_LB :
      RoughBlocks.Heavy.Numeric.margin m
        ≤ RoughBlocks.Heavy.Numeric.LB m (x : ℕ) :=
    RoughBlocks.Heavy.Numeric.LB_ge_margin' (m := m) (x := (x : ℕ)) hmU hx
  exact le_trans h_fL_le_margin (le_trans h_margin_le_LB h_LB_le_PhiDiff)

/-! ## 4. Fechamento de `h_base` e consequências formais -/

/-- `C1 > 0` em `ℝ`. -/
private lemma C1_pos : 0 < (RoughBlocks.External.Certs.UniformLB18794Bridge.C1_q : ℝ) :=
  by norm_num [RoughBlocks.External.Certs.UniformLB18794Bridge.C1_q]

/-- `vL ≥ 0` pois `(ω + C1)/(2ω)` com `ω>0`, `C1>0`. -/
private lemma vL_nonneg (x : Fin 9) : 0 ≤ vL x := by
  have hω : 0 < (omegaLo_q x : ℝ) := omegaLo_pos x
  have hden : 0 < (2 : ℝ) * (omegaLo_q x : ℝ) := mul_pos (by norm_num) hω
  have hnum : 0 ≤ (omegaLo_q x : ℝ) + (C1_q : ℝ) :=
    add_nonneg (le_of_lt hω) (le_of_lt C1_pos)
  exact (div_nonneg hnum hden.le)

/-- Monotonicidade de `fL` para `L₁ ≤ L₂` quando `vL ≤ L₁`. -/
private lemma fL_mono_on_right (x : Fin 9) {L₁ L₂ : ℝ}
  (hv₁ : vL x ≤ L₁) (h₁₂ : L₁ ≤ L₂) :
  fL x L₁ ≤ fL x L₂ := by
  have hω : 0 ≤ (omegaLo_q x : ℝ) := (omegaLo_pos x).le
  have a₁ : 0 ≤ L₁ - vL x := sub_nonneg.mpr hv₁
  have a₂ : 0 ≤ L₂ - vL x := sub_nonneg.mpr (le_trans hv₁ h₁₂)
  have hdiff : L₁ - vL x ≤ L₂ - vL x := sub_le_sub_right h₁₂ _
  have habs : |L₁ - vL x| ≤ |L₂ - vL x| := by
    simpa [abs_of_nonneg a₁, abs_of_nonneg a₂] using hdiff
  have hsq : (L₁ - vL x)^2 ≤ (L₂ - vL x)^2 := by
    simpa [pow_two] using (sq_le_sq.mpr habs)
  have hconst :
    (2*(C1_q : ℝ) - (omegaLo_q x : ℝ) * (vL x)^2)
      ≤ (2*(C1_q : ℝ) - (omegaLo_q x : ℝ) * (vL x)^2) := le_rfl
  simpa [fL] using add_le_add (mul_le_mul_of_nonneg_left hsq hω) hconst

/-- Bound puramente numérico: `2 ≤ fL(46/5)` (independe de `x`). -/
private lemma two_le_fL_at_46_over_5 (x : Fin 9) :
    (2 : ℝ) ≤ fL x ((46:ℝ)/5) := by
  -- termo quadrático
  have hv5 : vL x ≤ (5 : ℝ) := le_of_lt (vL_lt_five x)
  have a0 : 0 ≤ (46:ℝ)/5 - 5 := by norm_num
  have b0 : 0 ≤ (46:ℝ)/5 - vL x := by linarith [hv5]
  have a_le_b : (46:ℝ)/5 - 5 ≤ (46:ℝ)/5 - vL x := by linarith [hv5]
  have sq_a_le_sq_b :
      ((46:ℝ)/5 - 5)^2 ≤ ((46:ℝ)/5 - vL x)^2 := by
    have := mul_le_mul a_le_b a_le_b a0 b0
    simpa [pow_two] using this
  have hω : 0 ≤ (omegaLo_q x : ℝ) := (omegaLo_pos x).le
  have A1 :
      (omegaLo_q x : ℝ) * ((46:ℝ)/5 - 5)^2
        ≤ (omegaLo_q x : ℝ) * ((46:ℝ)/5 - vL x)^2 :=
    mul_le_mul_of_nonneg_left sq_a_le_sq_b hω

  -- termo negativo com `v^2 ≤ 25`
  have hv0 : 0 ≤ vL x := vL_nonneg x
  have v2_mul_le_25 : vL x * vL x ≤ (25 : ℝ) := by
    have h : vL x * vL x ≤ (5 : ℝ) * 5 :=
      mul_le_mul hv5 hv5 hv0 (by norm_num : (0:ℝ) ≤ 5)
    have h5 : (5 : ℝ) * 5 = (25 : ℝ) := by norm_num
    simpa [h5] using h
  have v2_le_25 : (vL x)^2 ≤ (25 : ℝ) := by
    simpa [pow_two] using v2_mul_le_25
  have B1 :
      -(omegaLo_q x : ℝ) * (25 : ℝ)
        ≤ -(omegaLo_q x : ℝ) * (vL x)^2 := by
    have : (omegaLo_q x : ℝ) * (vL x)^2 ≤ (omegaLo_q x : ℝ) * (25 : ℝ) :=
      mul_le_mul_of_nonneg_left v2_le_25 hω
    simpa [mul_comm] using (neg_le_neg this)

  -- base numérica e lift para `ω`,`C1`
  have base_num :
      (2 : ℝ) + (49/100 : ℝ) * 25
        ≤ (49/100 : ℝ) * ((46:ℝ)/5 - 5)^2 + (2 * (44/10 : ℝ)) := by
    norm_num
  have base :
      (2 : ℝ) + (omegaLo_q x : ℝ) * 25
        ≤ (omegaLo_q x : ℝ) * ((46:ℝ)/5 - 5)^2 + (2 * (C1_q : ℝ)) := by
    simpa [UniformLB18794Bridge.omegaLo_q, UniformLB18794Bridge.C1_q] using base_num

  -- soma final
  have base' :
      (2 : ℝ)
        ≤ (omegaLo_q x : ℝ) * ((46:ℝ)/5 - 5)^2 + (2 * (C1_q : ℝ)) + (-(omegaLo_q x : ℝ) * 25) := by
    have := add_le_add_right base (-(omegaLo_q x : ℝ) * (25 : ℝ))
    simpa [add_comm, add_left_comm, add_assoc, sub_eq_add_neg] using this

  have step :
      (omegaLo_q x : ℝ) * ((46:ℝ)/5 - 5)^2 + (2 * (C1_q : ℝ)) + (-(omegaLo_q x : ℝ) * 25)
        ≤ (omegaLo_q x : ℝ) * ((46:ℝ)/5 - vL x)^2 + (2 * (C1_q : ℝ)) + (-(omegaLo_q x : ℝ) * (vL x)^2) := by
    exact add_le_add (add_le_add A1 le_rfl) B1

  have : (2 : ℝ) ≤
      (omegaLo_q x : ℝ) * ((46:ℝ)/5 - vL x)^2 + (2 * (C1_q : ℝ)) + (-(omegaLo_q x : ℝ) * (vL x)^2) :=
    base'.trans step

  simpa [fL, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

/-- "Base sem hipótese": `rows(x) ≤ fL x (log m0)`. -/
lemma rows_le_fL_at_m0_no_hyp (x : Fin 9) :
  (finalLowerLo_of x : ℝ) ≤ fL x (Real.log (m0 : ℝ)) := by
  have h_rows_le_two : (finalLowerLo_of x : ℝ) ≤ 2 :=
    RoughBlocks.External.Certs.finalLowerLo_of_le_two x
  have h_two_le_fL_46 : (2 : ℝ) ≤ fL x ((46:ℝ)/5) :=
    two_le_fL_at_46_over_5 x
  have h46_le_4log10 : (46:ℝ)/5 ≤ 4 * Real.log (10:ℝ) := by
    have hlog10 :
        (23:ℝ) / 10 ≤ Real.log (10:ℝ) :=
      (Real.le_log_iff_exp_le (by norm_num)).mpr
        RoughBlocks.Heavy.Log10Bounds.exp_23_tenths_le_10
    have hmul : 4 * ((23:ℝ)/10) ≤ 4 * Real.log (10:ℝ) :=
      mul_le_mul_of_nonneg_left hlog10 (by norm_num : (0:ℝ) ≤ 4)
    have : (46:ℝ)/5 = 4 * ((23:ℝ)/10) := by norm_num
    simpa [this] using hmul
  have h4log10_le_logm0 :
      4 * Real.log (10:ℝ) ≤ Real.log (m0 : ℝ) :=
    four_log10_le_log_m0
  -- monotonicidade de `fL` à direita do vértice
  have hv46 : vL x ≤ (46:ℝ)/5 := by
    have hv5 : vL x ≤ (5:ℝ) := le_of_lt (vL_lt_five x)
    exact hv5.trans (by norm_num : (5:ℝ) ≤ (46:ℝ)/5)
  have step1 : fL x ((46:ℝ)/5) ≤ fL x (4 * Real.log (10:ℝ)) :=
    fL_mono_on_right x hv46 h46_le_4log10
  have step2 : fL x (4 * Real.log (10:ℝ)) ≤ fL x (Real.log (m0 : ℝ)) :=
    fL_mono_on_right x (le_trans hv46 h46_le_4log10) h4log10_le_logm0
  exact h_rows_le_two.trans (h_two_le_fL_46.trans (step1.trans step2))

/-- **Parametrizada**: `rows(x) ≤ fL x (log m0)` assumindo `10000 ≤ m0`. -/
lemma rows_le_fL_at_m0_no_hyp_of_10000_le (x : Fin 9)
  (h10000 : (10000 : ℕ) ≤ m0) :
  (finalLowerLo_of x : ℝ) ≤ fL x (Real.log (m0 : ℝ)) := by
  have h_rows_le_two : (finalLowerLo_of x : ℝ) ≤ 2 :=
    RoughBlocks.External.Certs.finalLowerLo_of_le_two x
  have h_two_le_fL_46 : (2 : ℝ) ≤ fL x ((46:ℝ)/5) :=
    two_le_fL_at_46_over_5 x
  have h46_le_4log10 : (46:ℝ)/5 ≤ 4 * Real.log (10:ℝ) := by
    have hlog10 :
        (23:ℝ) / 10 ≤ Real.log (10:ℝ) :=
      (Real.le_log_iff_exp_le (by norm_num)).mpr
        RoughBlocks.Heavy.Log10Bounds.exp_23_tenths_le_10
    have hmul : 4 * ((23:ℝ)/10) ≤ 4 * Real.log (10:ℝ) :=
      mul_le_mul_of_nonneg_left hlog10 (by norm_num : (0:ℝ) ≤ 4)
    have : (46:ℝ)/5 = 4 * ((23:ℝ)/10) := by norm_num
    simpa [this] using hmul
  have h4log10_le_logm0 :
      4 * Real.log (10:ℝ) ≤ Real.log (m0 : ℝ) :=
    four_log10_le_log_m0_of_10000_le h10000
  -- monotonicidade de `fL` à direita do vértice
  have hv46 : vL x ≤ (46:ℝ)/5 := by
    have hv5 : vL x ≤ (5:ℝ) := le_of_lt (vL_lt_five x)
    exact hv5.trans (by norm_num : (5:ℝ) ≤ (46:ℝ)/5)
  have step1 : fL x ((46:ℝ)/5) ≤ fL x (4 * Real.log (10:ℝ)) :=
    fL_mono_on_right x hv46 h46_le_4log10
  have step2 : fL x (4 * Real.log (10:ℝ)) ≤ fL x (Real.log (m0 : ℝ)) :=
    fL_mono_on_right x (le_trans hv46 h46_le_4log10) h4log10_le_logm0
  exact h_rows_le_two.trans (h_two_le_fL_46.trans (step1.trans step2))

/-! ## 5. Ponte e consequências (originais) -/

theorem phiDiff_ge_uniformLB_at_m0 (x : Fin 9) :
  ((PhiGE (m0*m0 + (x:ℕ)*m0 + m0) (m0+1) : ℝ)
   - (PhiGE (m0*m0 + (x:ℕ)*m0)       (m0+1) : ℝ))
  ≥ (uniformLB18794_finalLowerLo x : ℝ) := by
  have h_rows :
      ((PhiGE (m0*m0 + (x:ℕ)*m0 + m0) (m0+1) : ℝ)
       - (PhiGE (m0*m0 + (x:ℕ)*m0)     (m0+1) : ℝ))
      ≥ (finalLowerLo_of x : ℝ) :=
    phiDiff_ge_row_finalLowerLo_18794_ALL x
  exact le_trans (uniformLB_le_rows x) h_rows

theorem phiDiff_ge_rows_for_all_m_formal
  (x : Fin 9) {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  PhiDiffAt m (x : ℕ) ≥ (finalLowerLo_of x : ℝ) := by
  have h_base : (finalLowerLo_of x : ℝ) ≤ fL x (Real.log (m0 : ℝ)) :=
    rows_le_fL_at_m0_no_hyp x
  have hv_logm0 : vL x ≤ Real.log (m0 : ℝ) :=
    vL_le_logm0_of_bound x (le_of_lt (vL_lt_five x))
  have hmono : fL x (Real.log (m0 : ℝ)) ≤ fL x (Real.log (m : ℝ)) :=
    fL_mono_from_m0 x hm hv_logm0
  have hbridge : fL x (Real.log (m : ℝ)) ≤ PhiDiffAt m (x : ℕ) :=
    fL_le_PhiDiff (m := m) (hm := hmB) (x := x)
      (h_fL_le_margin := h_fL_le_margin)
      (h_LB_le_PhiDiff := h_LB_le_PhiDiff)
  exact h_base.trans (hmono.trans hbridge)

theorem phiDiff_ge_uniformLB_for_all_m_formal
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m) (x : Fin 9)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  PhiDiffAt m (x : ℕ) ≥ (uniformLB18794_finalLowerLo x : ℝ) := by
  have h_rows :
      PhiDiffAt m (x : ℕ) ≥ (finalLowerLo_of x : ℝ) :=
    phiDiff_ge_rows_for_all_m_formal x hmB hm h_fL_le_margin h_LB_le_PhiDiff
  exact (uniformLB_le_rows x).trans h_rows

/-- "Dois m-ásperos" (original, usa `by decide` e `native_decide`). -/
theorem two_mRough_in_block_for_all_m_formal
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m) (x : Fin 9)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  2 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ m0) hm
  have Hϕ : PhiDiffAt m (x : ℕ) ≥ (uniformLB18794_finalLowerLo x : ℝ) :=
    phiDiff_ge_uniformLB_for_all_m_formal hmB hm x h_fL_le_margin h_LB_le_PhiDiff
  have hUB1 : (uniformLB18794_finalLowerLo x : ℝ) > (1 : ℝ) := by
    have : uniformLB18794_finalLowerLo x > (1 : ℚ) := by
      fin_cases x <;> native_decide
    exact_mod_cast this
  have hΦ : (1 : ℝ) < PhiDiffAt m (x : ℕ) := lt_of_lt_of_le hUB1 Hϕ
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  have hEq := countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := (x : ℕ)) hm2 hx
  have : (1 : ℝ) < (countRoughInBlock m (x : ℕ) : ℝ) := by simpa [hEq] using hΦ
  have : 1 < countRoughInBlock m (x : ℕ) := by exact_mod_cast this
  exact Nat.succ_le_of_lt this

/-- Versão numérica (original). -/
theorem one_mRough_in_allNine_from_18794_ipth
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m)
  (hF : ∀ x : Fin 9, fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hL : ∀ x : Fin 9, RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  ∀ x : Fin 9, 1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  intro x
  have h2 := two_mRough_in_block_for_all_m_formal (m := m) hmB hm x (hF x) (hL x)
  exact (le_trans (by decide : 1 ≤ 2) h2)

/-! ## 6. DROP `hmB` (original) -/
theorem one_mRough_in_allNine_from_18794_drop_hmB
  {m : ℕ} (hm : m0 ≤ m)
  (hF : ∀ x : Fin 9, fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hL : ∀ x : Fin 9, RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  ∀ x : Fin 9, 1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  have hmB : BridgeThreshold ≤ m := le_trans bridgeThreshold_le_m0 hm
  exact one_mRough_in_allNine_from_18794_ipth (m := m) hmB hm hF hL

/-! ## 7. Versões GLOBAIS/ESTRUTURADAS para não passar `hF/hL` toda hora -/
structure UniformBridgeFrom_m0 : Prop :=
  (fL_le_margin_ge_m0 :
    ∀ {m : ℕ}, m0 ≤ m → ∀ x : Fin 9,
      fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (LB_le_PhiDiff_ge_m0 :
    ∀ {m : ℕ}, m0 ≤ m → ∀ x : Fin 9,
      RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ))

theorem one_mRough_in_allNine_from_18794_using_uniformBridge
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, 1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  refine one_mRough_in_allNine_from_18794_drop_hmB (m := m) hm ?hF ?hL
  · intro x; exact H.fL_le_margin_ge_m0 hm x
  · intro x; exact H.LB_le_PhiDiff_ge_m0 hm x

/-! ## 8. **VERSÕES PARAMETRIZADAS** (sem `decide/native_decide`) p/ cortar axiomas no final -/

/-- Ponte com `U0Default ≤ BridgeThreshold` como hipótese explícita. -/
theorem phiDiff_ge_rows_for_all_m_formal_param
  (hU0B : U0Default ≤ BridgeThreshold) (x : Fin 9) {m : ℕ}
  (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ))
  (h10000 : (10000 : ℕ) ≤ m0) :
  PhiDiffAt m (x : ℕ) ≥ (finalLowerLo_of x : ℝ) := by
  have h_base : (finalLowerLo_of x : ℝ) ≤ fL x (Real.log (m0 : ℝ)) :=
    rows_le_fL_at_m0_no_hyp_of_10000_le x h10000
  have hv_logm0 : vL x ≤ Real.log (m0 : ℝ) :=
    vL_le_logm0_of_bound_of_10000_le x (le_of_lt (vL_lt_five x)) h10000
  have hmono : fL x (Real.log (m0 : ℝ)) ≤ fL x (Real.log (m : ℝ)) :=
    fL_mono_from_m0 x hm hv_logm0
  have hbridge : fL x (Real.log (m : ℝ)) ≤ PhiDiffAt m (x : ℕ) :=
    fL_le_PhiDiff_of_hU0B (m := m) hU0B hm x h_fL_le_margin h_LB_le_PhiDiff
  exact h_base.trans (hmono.trans hbridge)

/-- “Dois m-ásperos” **parametrizado**: sem `decide/native_decide`. -/
theorem two_mRough_in_block_for_all_m_formal_param
  (hU0B : U0Default ≤ BridgeThreshold)
  (h2m0 : 2 ≤ m0) (hUB1 : ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1)
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m) (x : Fin 9)
  (hF : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hL : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ))
  (h10000 : (10000 : ℕ) ≤ m0) :
  2 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  have hm2 : 2 ≤ m := le_trans h2m0 hm
  have Hϕ : PhiDiffAt m (x : ℕ) ≥ (uniformLB18794_finalLowerLo x : ℝ) := by
    have : PhiDiffAt m (x : ℕ) ≥ (finalLowerLo_of x : ℝ) :=
      phiDiff_ge_rows_for_all_m_formal_param hU0B x hmB hm hF hL h10000
    exact (uniformLB_le_rows x).trans this
  have hUB1' : (1 : ℝ) < (uniformLB18794_finalLowerLo x : ℝ) := by
    have := hUB1 x
    have : (uniformLB18794_finalLowerLo x : ℝ) > (1 : ℝ) := this
    exact this
  have hΦ : (1 : ℝ) < PhiDiffAt m (x : ℕ) := lt_of_lt_of_le hUB1' Hϕ
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  have hEq := countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := (x : ℕ)) hm2 hx
  have : (1 : ℝ) < (countRoughInBlock m (x : ℕ) : ℝ) := by simpa [hEq] using hΦ
  have : 1 < countRoughInBlock m (x : ℕ) := by exact_mod_cast this
  exact Nat.succ_le_of_lt this

/-- “Pelo menos 1 m-áspero em cada bloco” **parametrizado** (sem `decide/native_decide`). -/
theorem one_mRough_in_allNine_from_18794_param
  (hU0B : U0Default ≤ BridgeThreshold)
  (h2m0 : 2 ≤ m0) (hUB1 : ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1)
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m)
  (hF_all : ∀ x : Fin 9, fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hL_all : ∀ x : Fin 9, RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ))
  (h10000 : (10000 : ℕ) ≤ m0) :
  ∀ x : Fin 9, 1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  intro x
  have h2 := two_mRough_in_block_for_all_m_formal_param hU0B h2m0 hUB1 (m := m) hmB hm x (hF_all x) (hL_all x) h10000
  exact (le_trans (by decide : 1 ≤ 2) h2)

/-- **Teorema final “estrito”**: sem `decide/native_decide` no caminho da prova.
Passe as premissas numéricas como hipóteses (ou agrupe em uma estrutura sua). -/
theorem one_mRough_in_allNine_from_18794_using_uniformBridge_strict
  (H : UniformBridgeFrom_m0)
  (hB0 : BridgeThreshold ≤ m0)                -- em vez de `bridgeThreshold_le_m0`
  (hU0B : U0Default ≤ BridgeThreshold)        -- em vez de `by decide`
  (h2m0 : 2 ≤ m0)                              -- em vez de `by decide`
  (h10000 : (10000 : ℕ) ≤ m0)                  -- em vez de `native_decide`
  (hUB1 : ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1) -- em vez de `native_decide`
  {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, 1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  -- remove `hmB` via hipótese explícita `hB0`
  have hmB : BridgeThreshold ≤ m := le_trans hB0 hm
  -- usa a versão parametrizada que não chama `decide/native_decide`
  refine one_mRough_in_allNine_from_18794_param
    hU0B h2m0 hUB1 (m := m) hmB hm
    (fun x => H.fL_le_margin_ge_m0 hm x)
    (fun x => H.LB_le_PhiDiff_ge_m0 hm x)
    h10000



/-- Versão “auto” que sanitiza as hipóteses: usa os fatos computacionais internos
para eliminar `hB0`, `hU0B`, `h2m0`, `h10000` e `hUB1` do chamador.
Ficam apenas `H : UniformBridgeFrom_m0` e `hm : m0 ≤ m`. -/
theorem one_mRough_in_allNine_from_18794_using_uniformBridge_auto
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : m0 ≤ m) (x : Fin 9) :
  1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  -- Deriva `BridgeThreshold ≤ m` internamente
  have hmB : BridgeThreshold ≤ m := (le_trans bridgeThreshold_le_m0 hm)
  -- Constrói as duas condições “de ponte” a partir do adaptador `H`
  have hF : ∀ y : Fin 9, fL y (Real.log (m : ℝ)) ≤ margin m :=
    fun y => H.fL_le_margin_ge_m0 hm y
  have hL : ∀ y : Fin 9, LB m (y : ℕ) ≤ PhiDiffAt m (y : ℕ) :=
    fun y => H.LB_le_PhiDiff_ge_m0 hm y
  -- Aplica o teorema base que já prova “pelo menos 1 áspero por bloco”
  exact one_mRough_in_allNine_from_18794_ipth (m := m) hmB hm hF hL x

/-- Versão “∀ x” se preferir consumir de uma vez só. -/
theorem one_mRough_in_allNine_from_18794_using_uniformBridge_auto_all
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, 1 ≤ ((K m (x : ℕ)).filter (mRough m)).card :=
by
  intro x
  exact one_mRough_in_allNine_from_18794_using_uniformBridge_auto H hm x





/-- Versão “ponto a ponto”: só precisa do adaptador `H` e de `hm : m0 ≤ m`. -/
theorem one_mRough_in_allNine_from_18794_using_uniformBridge_autox
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : m0 ≤ m) (x : Fin 9) :
  1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  -- usa `BridgeThreshold ≤ m0` + `hm` para fabricar `hmB : BridgeThreshold ≤ m`
  have hmB : BridgeThreshold ≤ m := (le_trans bridgeThreshold_le_m0 hm)
  -- duas condições de ponte vindas do adaptador
  have hF : ∀ y : Fin 9, fL y (Real.log (m : ℝ)) ≤ margin m :=
    fun y => H.fL_le_margin_ge_m0 hm y
  have hL : ∀ y : Fin 9, LB m (y : ℕ) ≤ PhiDiffAt m (y : ℕ) :=
    fun y => H.LB_le_PhiDiff_ge_m0 hm y
  -- aplica o teorema base já provado
  exact one_mRough_in_allNine_from_18794_ipth (m := m) hmB hm hF hL x

/-- Versão “∀ x” (sem precisar passar `x` na chamada). -/
theorem one_mRough_in_allNine_from_18794_using_uniformBridge_auto_allx
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, 1 ≤ ((K m (x : ℕ)).filter (mRough m)).card :=
by
  intro x
  exact one_mRough_in_allNine_from_18794_using_uniformBridge_autox H hm x

/-- Versão específica em `m = m0` (ainda mais limpa: nem `hm` precisa ser passado). -/
theorem one_mRough_in_allNine_at_m0_using_uniformBridge_auto
  (H : UniformBridgeFrom_m0) :
  ∀ x : Fin 9, 1 ≤ ((K m0 (x : ℕ)).filter (mRough m0)).card :=
by
  -- aqui `hm` é só `le_rfl : m0 ≤ m0`
  have hm : m0 ≤ m0 := le_rfl
  intro x
  simpa using
    (one_mRough_in_allNine_from_18794_using_uniformBridge_autox (m := m0) H hm x)


/-- EXISTÊNCIA (forma geral): para todo `m ≥ m0` e `x ≤ 8`,
existe um `k ∈ K m x` que é `mRough m`.  Depende apenas do adaptador `H`. -/
lemma exists_mRough_in_block_ge_m0_using_uniformBridge
  (H : UniformBridgeFrom_m0) {m x : ℕ}
  (hm : m0 ≤ m) (hx : x ≤ 8) :
  ∃ k ∈ K m x, mRough m k := by
  -- Convertemos `x ≤ 8` para um `x9 : Fin 9`
  let x9 : Fin 9 := ⟨x, Nat.lt_succ_of_le hx⟩
  -- Temos `1 ≤ card` do filtro pelo teorema “auto”
  have h1 :
      1 ≤ ((K m (x : ℕ)).filter (mRough m)).card :=
    one_mRough_in_allNine_from_18794_using_uniformBridge_auto H (m := m) hm x9
  -- `1 ≤ card` ⇔ `0 < card`
  have hpos :
      0 < ((K m x).filter (mRough m)).card :=
    (by simpa using h1) |> (fun h => (Nat.succ_le_iff.mp h))
  -- De `card_pos` obtemos um elemento do filtro
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  -- Abrimos a condição de pertencer ao filtro
  rcases Finset.mem_filter.mp hk with ⟨hkK, hkR⟩
  exact ⟨k, hkK, hkR⟩

/-- EXISTÊNCIA (wrapper numérico): se você quiser o enunciado com `18794 ≤ m`,
basta passar uma prova `h_m0_18794 : m0 = 18794` (se for definicional, use `rfl`). -/
lemma exists_mRough_in_block_ge_18794_using_uniformBridge
  (H : UniformBridgeFrom_m0) {m x : ℕ}
  (hm18794 : (18794 : ℕ) ≤ m) (hx : x ≤ 8)
  (h_m0_18794 : m0 = 18794) :
  ∃ k ∈ K m x, mRough m k := by
  -- Converte `18794 ≤ m` em `m0 ≤ m` via `m0 = 18794`
  have hm : m0 ≤ m := by simpa [h_m0_18794] using hm18794
  exact exists_mRough_in_block_ge_m0_using_uniformBridge H hm hx



-- /-- Para todo `m ≥ m0` e todo bloco `x : Fin 9`, existe um `m`-áspero em `K m x`. -/
-- theorem exists_allNine_ge_m0_using_uniformBridge
--   (H : UniformBridgeFrom_m0) {m : ℕ} (hm : m0 ≤ m) :
--   ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
--   intro x
--   have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
--   simpa using
--     exists_mRough_in_block_ge_m0_using_uniformBridge H (hm := hm) (hx := hx)



-- /-- Para todo `m ≥ m0` e todo bloco `x : Fin 9`, existe um `m`-áspero em `K m x`. -/
-- theorem exists_allNine_ge_m0_using_uniformBridge
--   -- passe as hipóteses necessárias (ou importe Parte01 para obtê-las como lemas)
--   (h2m0 : 2 ≤ m0)
--   (hUB1 : ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1)
--   -- “ponte plugada” (se você quiser usar o `H` da Parte 3, dá pra construir este Hplug; ver nota abaixo)
--   (Hplug : ∀ {m : ℕ}, m0 ≤ m → ∀ x : Fin 9,
--             (uniformLB18794_finalLowerLo x : ℝ) ≤ PhiDiffAt m (x : ℕ))
--   {m : ℕ} (hm : m0 ≤ m) :
--   ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
--   intro x
--   -- usa o lema “plug” da Parte 4
--   exact exists_allNine_ge_m0_using_plug
--           (h2m0 := h2m0) (hUB1 := hUB1) (Hplug := Hplug) hm x


/-- Versão “com H”: para todo `m ≥ m0` e todo bloco `x : Fin 9`,
    existe um `m`-áspero em `K m x`. -/
theorem exists_allNine_ge_m0_using_uniformBridge
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
  intro x
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  simpa using
    exists_mRough_in_block_ge_m0_using_uniformBridge H (hm := hm) (hx := hx)







theorem exists_allNine_ge_m0_using_uniformBridge_strict
  (H : UniformBridgeFrom_m0)
  (hB0 : BridgeThreshold ≤ m0) (hU0B : U0Default ≤ BridgeThreshold)
  (h2m0 : 2 ≤ m0) (h10000 : (10000 : ℕ) ≤ m0)
  (hUB1 : ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1)
  {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
  -- pega “1 por bloco” da sua versão parametrizada já provada
  have hmB : BridgeThreshold ≤ m := le_trans hB0 hm
  intro x
  have h1 :
      1 ≤ ((K m (x : ℕ)).filter (mRough m)).card :=
    one_mRough_in_allNine_from_18794_param
      hU0B h2m0 hUB1 (m := m) hmB hm
      (fun y => H.fL_le_margin_ge_m0 hm y)
      (fun y => H.LB_le_PhiDiff_ge_m0 hm y)
      h10000 x
  have hpos : 0 < ((K m (x : ℕ)).filter (mRough m)).card :=
    Nat.succ_le_iff.mp h1
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hpos
  rcases Finset.mem_filter.mp hk with ⟨hkK, hkR⟩
  exact ⟨k, hkK, hkR⟩




/-- Versão AUTO via *plug* (Parte 3): só precisa de `hm : m0 ≤ m`.
    Por dentro: usa `by decide` para `2 ≤ m0`, a tabela `uniformLB18794_gt_one` (Parte 1)
    e o plug `Hplug_uniformLB` (Parte 3) dentro do teorema plugado da Parte 4. -/
theorem exists_allNine_ge_m0_auto_plug_closed
  {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
  -- Parte 1: fatos computacionais
  have h2m0 : 2 ≤ m0 := by decide
  have hUB1 :
      ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1 :=
    RoughBlocks.External.Certs.uniformLB18794_gt_one
  -- Parte 4 (teorema plugado) + Parte 3 (plug)
  intro x
  exact RoughBlocks.External.Certs.exists_allNine_ge_m0_using_plug
          (h2m0 := h2m0) (hUB1 := hUB1)
          (Hplug := RoughBlocks.External.Certs.Hplug_uniformLB)
          hm x


theorem exists_allNine_ge_m0_auto_plug_closed_all
  {m : ℕ} (hm : m0 ≤ m) :
  ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k :=
by
  intro x
  exact exists_allNine_ge_m0_auto_plug_closed hm x




    #print axioms RoughBlocks.External.Certs.exists_allNine_ge_m0_auto_plug_closed_all
    #check RoughBlocks.External.Certs.exists_allNine_ge_m0_auto_plug_closed_all





end
end RoughBlocks.External.Certs
