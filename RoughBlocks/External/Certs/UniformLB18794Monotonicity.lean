/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Bridge
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.Heavy.Log10Bounds
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.Numeric

namespace RoughBlocks.External.Certs
noncomputable section
open Real
open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs
open RoughBlocks.External.Certs.UniformLB18794Bridge

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

/-! ## 1. Monotonicidades elementares -/

/-- Monotonicidade de `log` a partir de `m0` (versão em `ℕ`). -/
lemma log_mono_from_m0_nat {m : ℕ} (hm : m0 ≤ m) :
    Real.log (m0 : ℝ) ≤ Real.log (m : ℝ) := by
  have hm0posℝ : 0 < (m0 : ℝ) := by exact_mod_cast (by decide : 0 < m0)
  have hle : (m0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  exact Real.log_le_log hm0posℝ hle

  #print axioms RoughBlocks.External.Certs.log_mono_from_m0_nat

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

  #print axioms RoughBlocks.External.Certs.mono_sq_shift

/-- Versão direta para `L = log m` usando `m ≥ m0`. -/
lemma mono_main_from_m0_nat_of_cert
    (ω v : ℝ) {m : ℕ}
    (hm : m0 ≤ m) (hω : 0 ≤ ω) (hv : v ≤ Real.log (m0 : ℝ)) :
  ω * (Real.log (m0 : ℝ) - v)^2 ≤ ω * (Real.log (m : ℝ) - v)^2 := by
  have hlog : Real.log (m0 : ℝ) ≤ Real.log (m : ℝ) := log_mono_from_m0_nat hm
  exact mono_sq_shift ω v (Real.log (m0 : ℝ)) (Real.log (m : ℝ)) hω
    (by simpa using hv) hlog

    #print axioms RoughBlocks.External.Certs.mono_main_from_m0_nat_of_cert

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

  #print axioms RoughBlocks.External.Certs.fL_mono_from_m0

/-- Forma nomeada do lema anterior. -/
 theorem LB_from_cert_monotone_ge_m0 (x : Fin 9) {m : ℕ}
    (hm : m0 ≤ m) (hv : vL x ≤ Real.log (m0 : ℝ)) :
  fL x (Real.log (m0 : ℝ)) ≤ fL x (Real.log (m : ℝ)) :=
  fL_mono_from_m0 x hm hv

  #print axioms RoughBlocks.External.Certs.LB_from_cert_monotone_ge_m0

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

  #print axioms RoughBlocks.External.Certs.fL_mono_in_L_right_of_v

/-! ## 2. Bound `vL ≤ log m0` -/

/-- `4·log 10 ≤ log m0` (forma concreta para encadear `46/5 ≤ log m0`). -/
lemma four_log10_le_log_m0 : (4:ℝ) * Real.log (10:ℝ) ≤ Real.log (m0 : ℝ) := by
  have : (10000 : ℝ) ≤ (m0 : ℝ) := by exact_mod_cast (by native_decide : (10000 : ℕ) ≤ m0)
  calc
    (4:ℝ) * Real.log (10:ℝ) = Real.log ((10:ℝ)^4) := by rw [Real.log_pow, Nat.cast_ofNat]
    _ = Real.log (10000 : ℝ) := by norm_num
    _ ≤ Real.log (m0 : ℝ) := Real.log_le_log (by norm_num) this

    #print axioms RoughBlocks.External.Certs.four_log10_le_log_m0

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

  #print axioms RoughBlocks.External.Certs.five_le_log_m0

/-- De `vL ≤ 5` obtemos `vL ≤ log m0`. -/
lemma vL_le_logm0_of_bound (x : Fin 9) (hvl5 : vL x ≤ (5:ℝ)) :
  vL x ≤ Real.log (m0 : ℝ) :=
  hvl5.trans five_le_log_m0

  #print axioms RoughBlocks.External.Certs.vL_le_logm0_of_bound

/-- Versão em `ℕ` (para `x ≤ 8`). -/
lemma vL_le_logm0_nat {x : ℕ} (hx : x ≤ 8)
  (hvl5 : vL ⟨x, Nat.lt_succ_of_le hx⟩ ≤ (5:ℝ)) :
  vL ⟨x, Nat.lt_succ_of_le hx⟩ ≤ Real.log (m0 : ℝ) :=
  vL_le_logm0_of_bound ⟨x, Nat.lt_succ_of_le hx⟩ hvl5

  #print axioms RoughBlocks.External.Certs.vL_le_logm0_nat

/-! ## 3. Ponte via margem (faixa formal `m ≥ BridgeThreshold`) -/

/-- Para `m ≥ BridgeThreshold`, `fL(log m) ≤ Φ-dif(m,x)` assumindo `fL ≤ margin` e `LB ≤ Φ-dif`.
Encadeia `fL ≤ margin ≤ LB ≤ Φ-dif`. -/
lemma fL_le_PhiDiff
  {m : ℕ} (hm : BridgeThreshold ≤ m) (x : Fin 9)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  fL x (Real.log (m : ℝ)) ≤ PhiDiffAt m (x : ℕ) := by
  have hx  : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  -- usa `U0Default ≤ BridgeThreshold` (pode ser um lema ou `by decide`)
  have hmU : U0Default ≤ m :=
    (le_trans (by decide : U0Default ≤ BridgeThreshold) hm)
  have h_margin_le_LB :
      RoughBlocks.Heavy.Numeric.margin m
        ≤ RoughBlocks.Heavy.Numeric.LB m (x : ℕ) :=
    RoughBlocks.Heavy.Numeric.LB_ge_margin' (m := m) (x := (x : ℕ)) hmU hx
  exact le_trans h_fL_le_margin (le_trans h_margin_le_LB h_LB_le_PhiDiff)

  #print axioms RoughBlocks.External.Certs.fL_le_PhiDiff

/-! ## 4. Fechamento de `h_base` e consequências formais (sem hipóteses extras) -/

/-- `C1 > 0` em `ℝ` (sinais). -/
private lemma C1_pos : 0 < (RoughBlocks.External.Certs.UniformLB18794Bridge.C1_q : ℝ) :=
  by norm_num [RoughBlocks.External.Certs.UniformLB18794Bridge.C1_q]

  #print axioms C1_pos

/-- `vL ≥ 0` pois `(ω + C1)/(2ω)` com `ω>0`, `C1>0`. -/
private lemma vL_nonneg (x : Fin 9) : 0 ≤ vL x := by
  have hω : 0 < (omegaLo_q x : ℝ) := omegaLo_pos x
  have hden : 0 < (2 : ℝ) * (omegaLo_q x : ℝ) := mul_pos (by norm_num) hω
  have hnum : 0 ≤ (omegaLo_q x : ℝ) + (C1_q : ℝ) :=
    add_nonneg (le_of_lt hω) (le_of_lt C1_pos)
  exact (div_nonneg hnum hden.le)

  #print axioms vL_nonneg

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

  #print axioms fL_mono_on_right

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

  #print axioms two_le_fL_at_46_over_5

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

  #print axioms RoughBlocks.External.Certs.rows_le_fL_at_m0_no_hyp

/-! ## 5. Ponte uniforme — versões formais com `vL ≤ 5` -/

/-- Em `m0`: `Φ-dif ≥ uniformLB` (do framework `ALL`). -/
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

/-- Para `m ≥ BridgeThreshold` e `m ≥ m0`, obtemos `Φ-dif(m,x) ≥ rows(x)` sem usar `h_base`. -/
theorem phiDiff_ge_rows_for_all_m_formal
  (x : Fin 9) {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  PhiDiffAt m (x : ℕ) ≥ (finalLowerLo_of x : ℝ) := by
  -- base fechada: `rows ≤ fL(log m0)`
  have h_base : (finalLowerLo_of x : ℝ) ≤ fL x (Real.log (m0 : ℝ)) :=
    rows_le_fL_at_m0_no_hyp x
  -- monotonicidade em `m`: `vL ≤ log m0`
  have hv_logm0 : vL x ≤ Real.log (m0 : ℝ) :=
    vL_le_logm0_of_bound x (le_of_lt (vL_lt_five x))
  have hmono : fL x (Real.log (m0 : ℝ)) ≤ fL x (Real.log (m : ℝ)) :=
    fL_mono_from_m0 x hm hv_logm0
  -- ponte `fL ≤ margin ≤ LB ≤ Φ-dif`
  have hbridge : fL x (Real.log (m : ℝ)) ≤ PhiDiffAt m (x : ℕ) :=
    fL_le_PhiDiff (m := m) (hm := hmB) (x := x)
      (h_fL_le_margin := h_fL_le_margin)
      (h_LB_le_PhiDiff := h_LB_le_PhiDiff)
  exact h_base.trans (hmono.trans hbridge)

  #print axioms RoughBlocks.External.Certs.phiDiff_ge_rows_for_all_m_formal

/-- Para `m ≥ BridgeThreshold` e `m ≥ m0`, obtemos `Φ-dif(m,x) ≥ uniformLB(x)` sem hipóteses extras. -/
theorem phiDiff_ge_uniformLB_for_all_m_formal
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m) (x : Fin 9)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  PhiDiffAt m (x : ℕ) ≥ (uniformLB18794_finalLowerLo x : ℝ) := by
  have h_rows :
      PhiDiffAt m (x : ℕ) ≥ (finalLowerLo_of x : ℝ) :=
    phiDiff_ge_rows_for_all_m_formal x hmB hm h_fL_le_margin h_LB_le_PhiDiff
  exact (uniformLB_le_rows x).trans h_rows

  #print axioms RoughBlocks.External.Certs.phiDiff_ge_uniformLB_for_all_m_formal

/-- "Dois m-ásperos" na faixa formal (`m ≥ BridgeThreshold`, `m ≥ m0`), sem `h_base` nem `hvl5`. -/
theorem two_mRough_in_block_for_all_m_formal
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm : m0 ≤ m) (x : Fin 9)
  (h_fL_le_margin  : fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (h_LB_le_PhiDiff : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  2 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  -- `m ≥ 2` (pois `m ≥ m0` e `2 ≤ m0`)
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ m0) hm
  -- `Φ-dif ≥ uniformLB`
  have Hϕ : PhiDiffAt m (x : ℕ) ≥ (uniformLB18794_finalLowerLo x : ℝ) :=
    phiDiff_ge_uniformLB_for_all_m_formal hmB hm x h_fL_le_margin h_LB_le_PhiDiff
  -- `uniformLB(x) > 1` (computacional)
  have hUB1 : (uniformLB18794_finalLowerLo x : ℝ) > (1 : ℝ) := by
    have : uniformLB18794_finalLowerLo x > (1 : ℚ) := by
      fin_cases x <;> native_decide
    exact_mod_cast this
  -- então `Φ-dif > 1`
  have hΦ : (1 : ℝ) < PhiDiffAt m (x : ℕ) := lt_of_lt_of_le hUB1 Hϕ
  -- identifica `Φ-dif` com a contagem no bloco (`x ≤ 8`)
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  have hEq := countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := (x : ℕ)) hm2 hx
  have : (1 : ℝ) < (countRoughInBlock m (x : ℕ) : ℝ) := by simpa [hEq] using hΦ
  have : 1 < countRoughInBlock m (x : ℕ) := by exact_mod_cast this
  exact Nat.succ_le_of_lt this

  #print axioms RoughBlocks.External.Certs.two_mRough_in_block_for_all_m_formal

end
end RoughBlocks.External.Certs
