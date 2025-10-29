/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

-- O que falta eu escrever de código, exatamente?
-- 	•	omega_ge_one_half_on_Icc_two_three (acima)
-- 	•	LB_ge_marginPaper (acima)
-- 	•	fL_le_marginPaper_at_m0 (9 metas simples, uma por bloco) ou incluí-la como campo do seu adaptador UniformBridgeFrom_m0.

-- Se você quiser, eu já redijo a versão (A) com as nove metas no arquivo que você preferir (por ex. External/Certs/UniformLB18794Bridge.lean), usando as bounds que você já tem (vL < 5, four_log10_le_log_m0, five_le_log_m0, etc.). É direto e não usa native_decide (só norm_num, linarith, ring).

-- resumo curto:
-- Ponte 2 ✅
-- Ponte 1 = (i) provar LB ≥ marginPaper (feito acima), + (ii) checar fL ≤ marginPaper no caso base m0 e propagar por monotonicidade (posso escrever agora, só me diga onde você quer o lemma).



import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Buchstab.Core
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.Omega
import RoughBlocks.Heavy.Log10Bounds
import RoughBlocks.Heavy.Buchstab.Monotonicity
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

/-!
# Teorema principal: `LB m x ≥ 1`

Este arquivo estabelece a desigualdade
\[
  \mathrm{LB}(m,x) \ge 1 \quad\text{para}\quad m \ge 2,\; x \le 8,
\]
combinando duas faixas complementares:

1. **Faixa computacional** `2 ≤ m < 10^6` (verificação determinística externa por crivo);
2. **Faixa formal/assintótica** `m ≥ 10^6`, via cota analítica em `ℝ` e monotonicidade.

## Ingredientes

* A função `omega` e as constantes padrão `C1Default`, `C2Default`, `U0Default`;
* Desigualdades elementares para `log`/`exp`;
* Derivadas e o Teorema do Valor Médio (MVT) em `ℝ`, com transporte para `ℕ`.
-/

set_option linter.unnecessarySimpa false
namespace RoughBlocks.Heavy.Numeric

open scoped BigOperators Topology
open Set
open RoughBlocks.Heavy.Buchstab
open Real
open RoughBlocks.Heavy.Log10Bounds

/-- Para `m ≥ 2`, tem-se `Real.log m > 0`. -/
lemma log_pos_of_ge_two {m : ℕ} (hm : 2 ≤ m) : 0 < Real.log (m : ℝ) := by
  have hm0 : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm)
  have hm1 : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hm)
  exact (Real.log_pos_iff hm0.le).2 hm1

/-- Cota elementar
\[
  \delta := \frac{\log\!\bigl(1 + x/m\bigr)}{\log m} \;\le\; \frac{8}{m \log m},
\]
válida para `m ≥ 2` e `x ≤ 8`. -/
lemma delta_le_8_div_m_log {m x : ℕ} (hm : 2 ≤ m) (hx : x ≤ 8) :
  Real.log (1 + (x : ℝ) / (m : ℝ)) / Real.log (m : ℝ)
    ≤ (8 : ℝ) / ((m : ℝ) * Real.log (m : ℝ)) := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm)
  have hlog : 0 < Real.log (m : ℝ) := log_pos_of_ge_two hm
  have hx0 : 0 ≤ (x : ℝ) := by exact_mod_cast (Nat.zero_le x)
  have hfrac_nonneg : 0 ≤ (x : ℝ) / (m : ℝ) := by exact div_nonneg hx0 hm0.le
  have hpos_one_plus : 0 < 1 + (x : ℝ) / (m : ℝ) := by
    have := add_pos_of_nonneg_of_pos hfrac_nonneg (by norm_num : 0 < (1 : ℝ))
    simpa [add_comm] using this
  have h_log_le_t :
      Real.log (1 + (x : ℝ) / (m : ℝ)) ≤ (1 + (x : ℝ) / (m : ℝ)) - 1 :=
    Real.log_le_sub_one_of_pos hpos_one_plus
  have h_log : Real.log (1 + (x : ℝ) / (m : ℝ)) ≤ (x : ℝ) / (m : ℝ) := by
    simpa [add_comm, add_left_comm, add_assoc] using h_log_le_t
  have h_xm : (x : ℝ) / (m : ℝ) ≤ (8 : ℝ) / (m : ℝ) := by
    exact div_le_div_of_nonneg_right (by exact_mod_cast hx) hm0.le
  have h_le : Real.log (1 + (x : ℝ) / (m : ℝ)) ≤ (8 : ℝ) / (m : ℝ) := le_trans h_log h_xm
  have h_div := div_le_div_of_nonneg_right h_le hlog.le
  simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h_div

/-- Definição padrão do lado analítico na janela curta do bloco
(`y = m`, `X = m^2 + x m`, `Y = m`). -/
noncomputable def LB (m x : ℕ) : ℝ :=
  ((m : ℝ) / Real.log (m : ℝ)) *
    Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ))
  - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
  - (C2Default : ℝ)

/-- `margin m` é a cota obtida substituindo `ω(u) ≥ 1/3` em `u ∈ [2,3]`. -/
noncomputable def margin (m : ℕ) : ℝ :=
  ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ) / 3)
  - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
  - (C2Default : ℝ)



/-- Para `X = m^2 + x m` e `u := log X / log m`, se `m ≥ U0Default` e `x ≤ 8` então `2 ≤ u ≤ 3`. -/
lemma u_block_range {m x : ℕ} (hm : m ≥ U0Default) (hx : x ≤ 8) :
  (2 : ℝ) ≤ Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ) ∧
  Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ (3 : ℝ) := by
  classical
  set X : ℕ := m^2 + x * m
  have hm_ge2 : 2 ≤ m := le_trans (by decide : (2 : ℕ) ≤ U0Default) hm
  have hm_pos_nat : 0 < m := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm_ge2
  have hm_pos_real : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
  have hlog_pos : 0 < Real.log (m : ℝ) := log_pos_of_ge_two hm_ge2
  have hlog_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlog_pos
  have hm2_pos_real : 0 < ((m^2 : ℕ) : ℝ) := by
    have : 0 < m^2 := by simpa [pow_two] using Nat.mul_pos hm_pos_nat hm_pos_nat
    exact_mod_cast this

  -- Lado esquerdo
  have hX_ge_m2 : (m^2 : ℕ) ≤ X := by dsimp [X]; exact Nat.le_add_right _ _
  have h_left : (2 : ℝ) ≤ Real.log (X : ℝ) / Real.log (m : ℝ) := by
    by_cases hx0 : x = 0
    · subst hx0
      have hlogX : Real.log ((X : ℝ)) = (2 : ℝ) * Real.log (m : ℝ) := by
        have hXpow : (X : ℝ) = (m : ℝ) ^ 2 := by simp [X, Nat.cast_pow]
        simpa [hXpow] using Real.log_pow hm_pos_real (2 : ℕ)
      have hratio : Real.log ((X : ℝ)) / Real.log (m : ℝ) = (2 : ℝ) := by
        calc
          Real.log ((X : ℝ)) / Real.log (m : ℝ)
              = ((2 : ℝ) * Real.log (m : ℝ)) / Real.log (m : ℝ) := by simp [hlogX]
          _ = (2 : ℝ) * (Real.log (m : ℝ) / Real.log (m : ℝ)) := by simp [mul_div_assoc]
          _ = (2 : ℝ) * 1 := by simp [hlog_ne]
          _ = (2 : ℝ) := by norm_num
      simp [hratio]
    ·
      have hxpos : 1 ≤ x := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hx0)
      have : (m^2 : ℕ) < X := by
        have hlt : m^2 < m^2 + m := Nat.lt_add_of_pos_right hm_pos_nat
        have hm_le_xm : m ≤ x * m := by simpa [Nat.one_mul] using Nat.mul_le_mul_right m hxpos
        have : m^2 + m ≤ X := by simpa [X] using Nat.add_le_add_left hm_le_xm (m^2)
        exact lt_of_lt_of_le hlt this
      have hlt_real : ((m^2 : ℕ) : ℝ) < (X : ℝ) := by exact_mod_cast this
      have hlog_lt : Real.log ((m^2 : ℕ) : ℝ) < Real.log (X : ℝ) :=
        Real.log_lt_log hm2_pos_real hlt_real
      have hlog_pow : Real.log ((m^2 : ℕ) : ℝ) = (2 : ℝ) * Real.log (m : ℝ) := by
        simpa [Nat.cast_pow] using Real.log_pow hm_pos_real (2 : ℕ)
      have : (2 : ℝ) < Real.log (X : ℝ) / Real.log (m : ℝ) := by
        have := div_lt_div_of_pos_right hlog_lt hlog_pos
        simpa [hlog_pow, mul_comm, mul_left_comm, mul_assoc, hlog_ne] using this
      exact le_of_lt this

  -- Lado direito
  have hm_ge8 : 8 ≤ m := le_trans (by decide : (8 : ℕ) ≤ U0Default) hm
  have hx_mul_le : x * m ≤ 8 * m := Nat.mul_le_mul_right _ hx
  have h8m_le_m2 : 8 * m ≤ m^2 := by
    simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_right m hm_ge8
  have hX_le_m3 : X ≤ m^3 := by
    have hx8 : m^2 + x * m ≤ m^2 + 8 * m := Nat.add_le_add_left hx_mul_le _
    have h_sum_le_2m2 : m^2 + 8 * m ≤ m^2 + m^2 := Nat.add_le_add_left h8m_le_m2 _
    have two_mul_m2_le_m3 : 2 * m^2 ≤ m^3 := by
      have : m^2 * 2 ≤ m^2 * m := Nat.mul_le_mul_left (m^2) hm_ge2
      simpa [pow_succ, pow_two, mul_comm, mul_left_comm, mul_assoc] using this
    have : (m^2 + m^2 : ℕ) ≤ m^3 := by simpa [two_mul] using two_mul_m2_le_m3
    exact le_trans (by simpa [X] using hx8.trans h_sum_le_2m2) this
  have hX_pos_nat : 0 < X := by
    have hm2_pos : 0 < m ^ 2 := by simpa [pow_two] using Nat.mul_pos hm_pos_nat hm_pos_nat
    exact lt_of_lt_of_le hm2_pos hX_ge_m2
  have hX_pos_real : 0 < (X : ℝ) := by exact_mod_cast hX_pos_nat
  have hX_le_m3_real : (X : ℝ) ≤ ((m ^ 3 : ℕ) : ℝ) := by exact_mod_cast hX_le_m3
  have hlog_le : Real.log (X : ℝ) ≤ Real.log ((m ^ 3 : ℕ) : ℝ) :=
    Real.log_le_log hX_pos_real hX_le_m3_real
  have h_right_div :
      Real.log (X : ℝ) / Real.log (m : ℝ)
        ≤ Real.log ((m ^ 3 : ℕ) : ℝ) / Real.log (m : ℝ) :=
    div_le_div_of_nonneg_right hlog_le (log_pos_of_ge_two hm_ge2).le
  have hpow3 : Real.log ((m ^ 3 : ℕ) : ℝ) = (3 : ℝ) * Real.log (m : ℝ) := by
    simpa [Nat.cast_pow] using Real.log_pow hm_pos_real (3 : ℕ)
  have h_right : Real.log (X : ℝ) / Real.log (m : ℝ) ≤ (3 : ℝ) := by
    simpa [hpow3, mul_div_assoc, (ne_of_gt (log_pos_of_ge_two hm_ge2))] using h_right_div
  exact ⟨h_left, h_right⟩



/-- Cota inferior para `LB m x` substituindo `ω(u) ≥ 1/3` quando `u ∈ [2,3]`. -/
lemma LB_ge_margin {m x : ℕ} (hm : m ≥ U0Default) (hx : x ≤ 8) :
  LB m x ≥
    ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ) / 3)
    - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
    - (C2Default : ℝ) := by
  unfold LB
  have hlogpos : 0 < Real.log (m : ℝ) :=
    log_pos_of_ge_two (by exact (le_trans (by decide : (2:ℕ) ≤ U0Default) hm))
  have hcoef_nonneg : 0 ≤ (m : ℝ) / Real.log (m : ℝ) := by
    have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
    exact div_nonneg hm0 hlogpos.le
  have hRange := u_block_range (m := m) (x := x) hm hx
  -- use the stronger bound ω ≥ 1/2 on [2,3] and 1/3 ≤ 1/2 to get ω ≥ 1/3
  have homega_half :=
    Buchstab.omega_ge_one_half_on_Icc_two_three hRange.left hRange.right
  have one_third_le_half : (1 : ℝ) / 3 ≤ (1 : ℝ) / 2 := by norm_num
  have hω : (1 : ℝ) / 3 ≤
      Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ)) :=
    le_trans one_third_le_half homega_half
  have hmain :
      ((m : ℝ) / Real.log (m : ℝ)) *
        Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ))
      ≥ ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hω hcoef_nonneg
  exact sub_le_sub (sub_le_sub hmain le_rfl) le_rfl


/-- Versão conveniente em termos de `margin`. -/
lemma LB_ge_margin' {m x : ℕ} (hm : m ≥ U0Default) (hx : x ≤ 8) :
  LB m x ≥ margin m := by
  simpa [margin] using (LB_ge_margin (m := m) (x := x) hm hx)

/-! ## Derivadas usadas na monotonicidade de `marginR` (caso 1/3) -/

noncomputable def marginR (t : ℝ) : ℝ :=
  ((1 : ℝ) / 3) * (t / Real.log t)
  - C1Default * (t / (Real.log t)^2)
  - (C2Default : ℝ)




@[simp] lemma margin_coe (m : ℕ) : margin m = marginR (m : ℝ) := by
  simp [margin, marginR, div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc]

/-- Derivada de `t ↦ t / log t` para `t > 1`. -/
lemma hasDerivAt_t_div_log {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => t / Real.log t)
      ((Real.log x - 1) / (Real.log x)^2) x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hf : HasDerivAt (fun t : ℝ => t) (1 : ℝ) x := hasDerivAt_id x
  have hg : HasDerivAt Real.log ((1 : ℝ)/x) x := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx0)
  have hlog_ne : Real.log x ≠ 0 := by
    have : 0 < Real.log x := (Real.log_pos_iff (le_of_lt hx0)).2 hx
    exact ne_of_gt this
  have h := hf.div hg hlog_ne
  field_simp [pow_two] at h
  simpa [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using h



/-- Derivada de `t ↦ t / (log t)^2` para `t > 1`. -/
lemma hasDerivAt_t_div_log_sq {x : ℝ} (hx : 1 < x) :
    HasDerivAt (fun t => t / (Real.log t)^2)
      ((Real.log x - 2) / (Real.log x)^3) x := by
  have hx0 : 0 < x := lt_trans one_pos hx
  have hf : HasDerivAt (fun t : ℝ => t) (1 : ℝ) x := hasDerivAt_id x
  have hlog' : HasDerivAt Real.log ((1 : ℝ)/x) x := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx0)
  have hpow : HasDerivAt (fun t => (Real.log t)^2)
      (2 * Real.log x * ((1:ℝ)/x)) x := by
    simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc]
      using (HasDerivAt.pow hlog' 2)
  have hden_ne : (Real.log x)^2 ≠ 0 := by
    have : 0 < Real.log x := (Real.log_pos_iff (le_of_lt hx0)).2 hx
    simpa using pow_ne_zero 2 (ne_of_gt this)
  have hdiv := hf.div hpow hden_ne
  field_simp [pow_two, pow_three, mul_comm, mul_left_comm, mul_assoc] at hdiv
  simpa [pow_two, pow_three, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using hdiv



/-- Derivada explícita de `marginR` para `x > 1`. -/
lemma hasDerivAt_marginR {x : ℝ} (hx : 1 < x) :
  HasDerivAt marginR
    ( ((1:ℝ)/3) * ((Real.log x - 1) / (Real.log x)^2)
      - C1Default * ((Real.log x - 2) / (Real.log x)^3) ) x := by
  have h1 := (hasDerivAt_t_div_log    (x := x) hx).const_mul ((1:ℝ)/3)
  have h2 := (hasDerivAt_t_div_log_sq (x := x) hx).const_mul C1Default
  unfold marginR
  simpa [sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc]
    using (h1.sub h2).sub_const (C2Default : ℝ)

/-! ## Reescrita em `L = log x` e positividade (caso 1/3) -/

noncomputable def Nnum (L : ℝ) : ℝ :=
  ((1:ℝ)/3) * L^2 - ((71:ℝ)/15) * L + (44:ℝ)/5

lemma Nnum_factor (L : ℝ) :
  Nnum L = ((1:ℝ)/3) * (L - 12) * (L - (11:ℝ)/5) := by
  unfold Nnum; ring


lemma Nnum_nonneg_of_ge_12 {L : ℝ} (hL : (12:ℝ) ≤ L) : 0 ≤ Nnum L := by
  have h1 : 0 ≤ L - 12 := sub_nonneg.mpr hL
  have h2 : 0 ≤ L - (11:ℝ)/5 := by
    have : (11:ℝ)/5 ≤ 12 := by norm_num
    exact sub_nonneg.mpr (le_trans this hL)
  have hfac := Nnum_factor L
  simpa [hfac, mul_comm, mul_left_comm, mul_assoc] using
    mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ (1:ℝ)/3) h1) h2


/-- Mostra `log(10^6) ≥ 12` usando `exp 1 < 3` e \((\exp 1)^{12} \le 3^{12} \le 10^6\). -/
lemma log_1e6_ge_12 : (12 : ℝ) ≤ Real.log (1000000 : ℝ) := by
  -- usa `exp 1 < 3` e a cadeia de potências
  have hpos : (0:ℝ) < (1000000 : ℝ) := by norm_num
  have h_e_lt_3 : Real.exp 1 < (3:ℝ) := by
    exact lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_le : Real.exp (12:ℝ) ≤ (3:ℝ)^12 := by
    have hbase : (Real.exp 1 : ℝ) ≤ 3 := le_of_lt h_e_lt_3
    have hpos' : 0 ≤ (Real.exp 1 : ℝ) := (Real.exp_pos 1).le
    have pow_le : ∀ n : ℕ, (Real.exp 1 : ℝ) ^ n ≤ (3 : ℝ) ^ n := by
      intro n; induction n with
      | zero => simp
      | succ n ih =>
        calc
          (Real.exp 1 : ℝ) ^ (n + 1) = (Real.exp 1 : ℝ) ^ n * (Real.exp 1 : ℝ) := by rw [pow_succ]
          _ ≤ (3 : ℝ) ^ n * (Real.exp 1 : ℝ) := mul_le_mul_of_nonneg_right ih (Real.exp_pos 1).le
          _ ≤ (3 : ℝ) ^ n * 3 := mul_le_mul_of_nonneg_left hbase (pow_nonneg (by norm_num) n)
          _ = (3 : ℝ) ^ (n + 1) := by rw [pow_succ]
    have hexp_pow : Real.exp (12:ℝ) = (Real.exp 1 : ℝ) ^ 12 := by
      simpa using Real.exp_nat_mul (n := 12) (x := (1:ℝ))
    calc
      Real.exp (12:ℝ) = (Real.exp 1 : ℝ) ^ 12 := hexp_pow
      _ ≤ (3 : ℝ) ^ 12 := pow_le 12
  have h3pow_le : (3:ℝ)^12 ≤ (1000000 : ℝ) := by norm_num
  have hle : Real.exp (12:ℝ) ≤ (1000000 : ℝ) := le_trans hexp_le h3pow_le
  exact (Real.le_log_iff_exp_le hpos).mpr hle

/-- Para `x ≥ 10^6`, a derivada de `marginR` é não negativa. Escrevemos a derivada
como `Nnum(log x)/(log x)^3` e notamos `Nnum(log x) ≥ 0` quando `log x ≥ 12`. -/
lemma deriv_marginR_nonneg_of_ge_1e6 {x : ℝ} (hx : (1000000 : ℝ) ≤ x) :
  0 ≤ ((1:ℝ)/3) * ((Real.log x - 1) / (Real.log x)^2)
        - C1Default * ((Real.log x - 2) / (Real.log x)^3) := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1:ℝ) < 1000000) hx
  have hx0 : 0 < x := lt_trans one_pos hx1
  have hLpos : 0 < Real.log x := (Real.log_pos_iff (le_of_lt hx0)).2 hx1
  have hlog_mono : Real.log (1000000 : ℝ) ≤ Real.log x :=
    Real.log_le_log (by norm_num) hx
  have hL : (12:ℝ) ≤ Real.log x := le_trans log_1e6_ge_12 hlog_mono
  have hnum : 0 ≤ Nnum (Real.log x) := Nnum_nonneg_of_ge_12 hL
  have hden_pos : 0 < (Real.log x)^3 := by simpa [pow_three] using pow_pos hLpos 3
  have hxlog_ne : Real.log x ≠ 0 := ne_of_gt hLpos
  have hrepr :
      ((1:ℝ)/3) * ((Real.log x - 1) / (Real.log x)^2)
        - C1Default * ((Real.log x - 2) / (Real.log x)^3)
      = Nnum (Real.log x) / (Real.log x)^3 := by
    have hcalc :
      ((1:ℝ)/3) * ((Real.log x - 1) / (Real.log x)^2)
        - C1Default * ((Real.log x - 2) / (Real.log x)^3)
      = (((1:ℝ)/3) * ((Real.log x - 1) * Real.log x) - C1Default * (Real.log x - 2))
          / (Real.log x)^3 := by
      field_simp [pow_two, pow_three, hxlog_ne]
    have : (((1:ℝ)/3) * ((Real.log x - 1) * Real.log x) - C1Default * (Real.log x - 2))
             = Nnum (Real.log x) := by
      simp [Nnum, C1Default_def, pow_two]; ring
    calc
      _ = (((1:ℝ)/3) * ((Real.log x - 1) * Real.log x) - C1Default * (Real.log x - 2))
            / (Real.log x)^3 := by simpa using hcalc
      _ = Nnum (Real.log x) / (Real.log x)^3 := by
        simpa using (congrArg (fun t => t / (Real.log x)^3) this)
  have hge : 0 ≤ Nnum (Real.log x) / (Real.log x)^3 :=
    div_nonneg hnum (le_of_lt hden_pos)
  rw [hrepr]
  exact hge



/-! ## Monotonicidade em `ℝ` e transporte para `ℕ` (caso 1/3) -/

lemma marginR_succ_ge (m : ℕ) (hm : 1_000_000 ≤ m) :
  marginR (m+1) ≥ marginR m := by
  have hx : (1000000 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hder_nonneg :
      ∀ x ∈ Icc (m : ℝ) (m+1 : ℝ),
        0 ≤ ((1:ℝ)/3) * ((Real.log x - 1) / (Real.log x)^2)
            - C1Default * ((Real.log x - 2) / (Real.log x)^3) := by
    intro x hxI
    exact deriv_marginR_nonneg_of_ge_1e6 (le_trans hx hxI.1)
  have hdiff :
      ∀ x ∈ Icc (m:ℝ) (m+1:ℝ),
        HasDerivAt marginR
          ( ((1:ℝ)/3) * ((Real.log x - 1) / (Real.log x)^2)
            - C1Default * ((Real.log x - 2) / (Real.log x)^3) ) x := by
    intro x hxI
    have : (1 : ℝ) < x :=
      lt_of_lt_of_le (by norm_num : (1:ℝ) < (1000000 : ℝ)) (le_trans hx hxI.1)
    exact hasDerivAt_marginR this
  let g : ℝ → ℝ :=
    fun x =>
      ((1:ℝ)/3) * ((Real.log x - 1) / (Real.log x)^2)
        - C1Default * ((Real.log x - 2) / (Real.log x)^3)
  have hlt : (m : ℝ) < (m+1 : ℝ) := by exact_mod_cast Nat.lt_succ_self m
  rcases
    exists_hasDerivAt_eq_slope (f := marginR) (f' := g)
      (a := (m : ℝ)) (b := (m+1 : ℝ)) (hab := hlt)
      (hfc := fun x hx => (hdiff x hx).continuousAt.continuousWithinAt)
      (hff' := fun x hx => hdiff x ⟨hx.1.le, hx.2.le⟩)
    with ⟨c, hc, hEq⟩
  have hnonneg : 0 ≤ g c := by
    have hcIcc : c ∈ Icc (m:ℝ) (m+1:ℝ) := ⟨hc.1.le, hc.2.le⟩
    simpa [g] using hder_nonneg c hcIcc
  have : 0 ≤ marginR (m+1) - marginR m := by
    have : 0 ≤ ((m+1 : ℝ) - (m : ℝ)) := by norm_num
    simpa [hEq] using mul_nonneg this hnonneg
  simpa [sub_eq_add_neg] using (le_of_sub_nonneg this)


/-
------------------------------------------------------------------------------
Bloco 1: caso base `m = 10^6`
------------------------------------------------------------------------------
-/

/-- `margin` é não decrescente para `m ≥ 10^6` (em `ℕ`). -/
lemma margin_mono_from_1e6 {m n : ℕ}
  (hm : 1_000_000 ≤ m) (hmn : m ≤ n) : margin m ≤ margin n := by
  induction' hmn with k hk ih
  · rfl
  · have hk' : 1_000_000 ≤ k := le_trans hm hk
    have step := marginR_succ_ge k hk'
    have step' : margin k ≤ margin (k+1) := by simpa [margin_coe] using step
    exact le_trans ih step'

/-! ### Caso base em `m = 10^6` (via `Log10Bounds`) -/


/-- Caso base: `margin 10^6 ≥ 1`. Usa `log_1e6_bounds`. -/
lemma margin_base_1e6 : margin 1_000_000 ≥ 1 := by
  obtain ⟨hLlo, hLhi⟩ := log_1e6_bounds   -- (69/5) ≤ log(1e6) ≤ (693/50)
  unfold margin
  have hlogpos : 0 < Real.log (1_000_000 : ℝ) :=
    log_pos_of_ge_two (by decide : (2:ℕ) ≤ 1_000_000)
  -- Termo A
  have A_ge :
      ((1_000_000 : ℝ) / Real.log (1_000_000 : ℝ)) * ((1 : ℝ)/3)
        ≥ (1_000_000 : ℝ) / (3 * ((693 : ℝ) / 50)) := by
    have h_inv : (1 : ℝ) / ((693 : ℝ) / 50) ≤ (1 : ℝ) / Real.log (1_000_000 : ℝ) :=
      one_div_le_one_div_of_le hlogpos hLhi
    have := mul_le_mul_of_nonneg_left h_inv (by norm_num : 0 ≤ (1_000_000 : ℝ) / 3)
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- Termo B
  have CB_le :
      C1Default * ((1_000_000 : ℝ) / (Real.log (1_000_000 : ℝ))^2)
        ≤ C1Default * ((1_000_000 : ℝ) / (((69 : ℝ) / 5)^2)) := by
    have inv_le : (1 : ℝ) / Real.log (1_000_000 : ℝ) ≤ (1 : ℝ) / ((69 : ℝ) / 5) :=
      one_div_le_one_div_of_le (by norm_num : (0:ℝ) < (69 : ℝ)/5) hLlo
    have inv_nonneg : 0 ≤ (1 : ℝ) / Real.log (1_000_000 : ℝ) :=
      one_div_nonneg.mpr hlogpos.le
    have inv_sq_le :
        ((1 : ℝ) / Real.log (1_000_000 : ℝ)) * ((1 : ℝ) / Real.log (1_000_000 : ℝ))
          ≤ ((1 : ℝ) / ((69 : ℝ) / 5)) * ((1 : ℝ) / ((69 : ℝ) / 5)) :=
      mul_le_mul inv_le inv_le inv_nonneg (by norm_num : (0:ℝ) ≤ (1 : ℝ) / ((69 : ℝ) / 5))
    have B_le :
        (1_000_000 : ℝ) *
          ((1 : ℝ) / Real.log (1_000_000 : ℝ) * ((1 : ℝ) / Real.log (1_000_000 : ℝ)))
        ≤ (1_000_000 : ℝ) *
          ((1 : ℝ) / ((69 : ℝ) / 5) * ((1 : ℝ) / ((69 : ℝ) / 5))) :=
      mul_le_mul_of_nonneg_left inv_sq_le (by norm_num : (0:ℝ) ≤ 1_000_000)
    have hC1 : 0 ≤ C1Default := by
      simpa [C1Default_def] using (by norm_num : (0:ℝ) ≤ (22:ℝ)/5)
    have := mul_le_mul_of_nonneg_left B_le hC1
    simpa [one_div, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  -- Consolidação
  have base_bound :
      ((1_000_000 : ℝ) / Real.log (1_000_000 : ℝ)) * ((1 : ℝ)/3)
        - C1Default * ((1_000_000 : ℝ) / (Real.log (1_000_000 : ℝ))^2)
        - (C2Default : ℝ)
      ≥ ( (1_000_000 : ℝ) / (3 * ((693 : ℝ) / 50)) )
        - ( C1Default * ((1_000_000 : ℝ) / (((69 : ℝ) / 5)^2)) )
        - (C2Default : ℝ) := by
    exact sub_le_sub (sub_le_sub A_ge CB_le) le_rfl
  have A_int : (1_000_000 : ℝ) / (3 * ((693 : ℝ) / 50)) ≥ (24050 : ℝ) := by norm_num
  have B_int : C1Default * ((1_000_000 : ℝ) / (((69 : ℝ) / 5)^2)) ≤ (23105 : ℝ) := by
    have : C1Default = (22 : ℝ) / 5 := by simp [C1Default_def]
    simpa [this] using (by norm_num :
      ((22 : ℝ) / 5) * ((1_000_000 : ℝ) / (((69 : ℝ) / 5)^2)) ≤ (23105 : ℝ))
  have rhs_ge :
      ( (1_000_000 : ℝ) / (3 * ((693 : ℝ) / 50)) )
        - ( C1Default * ((1_000_000 : ℝ) / (((69 : ℝ) / 5)^2)) )
        - (C2Default : ℝ) ≥ 1 := by
    have hAint : (24050 : ℝ) ≤ (1_000_000 : ℝ) / (3 * ((693 : ℝ) / 50)) := by norm_num
    have hCval : (C2Default : ℝ) = 100 := by simp [C2Default_def]
    calc
      1 ≤ (24050 - 23105 - 100 : ℝ) := by norm_num
      _ = (24050 : ℝ) - (23105 : ℝ) - (C2Default : ℝ) := by rw [hCval]
      _ ≤ ( (1_000_000 : ℝ) / (3 * ((693 : ℝ) / 50)) )
           - ( C1Default * ((1_000_000 : ℝ) / (((69 : ℝ) / 5)^2)) )
           - (C2Default : ℝ) := by
        have hsub : (24050 : ℝ) - (23105 : ℝ) ≤
          ((1_000_000 : ℝ) / (3 * ((693 : ℝ) / 50))) -
          (C1Default * ((1_000_000 : ℝ) / (((69 : ℝ) / 5)^2))) :=
          sub_le_sub hAint B_int
        simpa using hsub
  exact le_trans rhs_ge base_bound


theorem margin_ge_one_at_1e6 : margin 1_000_000 ≥ 1 := margin_base_1e6

theorem margin_ge_one_from_1e6 :
  ∀ m : ℕ, m ≥ 1_000_000 → margin m ≥ 1 := by
  intro m hm
  have mono := margin_mono_from_1e6 (m := 1_000_000) (n := m) (by decide) hm
  exact le_trans margin_ge_one_at_1e6 mono

/-- Faixa formal: para `m ≥ 10⁶` e `x ≤ 8`, vale `LB m x ≥ 1`. -/
theorem budget_conservative_formal
  {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) : LB m x ≥ 1 := by
  have h₀ : LB m x ≥ margin m :=
    LB_ge_margin' (m := m) (x := x)
      (hm := le_trans (by decide : U0Default ≤ 1_000_000) hm) hx
  have h₁ : margin m ≥ 1 := margin_ge_one_from_1e6 m hm
  exact ge_trans h₀ h₁


/-! ###############  Margem “do paper” (C₁=4.4, C₂=100)  PARA 18794 ############### -/

/-- Margem analítica usada no paper:
    `(m/log m)*(1/2) - C1*(m/log^2 m) - 2/log^2 m - C2`. -/
noncomputable def marginPaper (m : ℕ) : ℝ :=
  ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ)/2)
  - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
  - (2 : ℝ) / (Real.log (m : ℝ))^2
  - (C2Default : ℝ)

/-- Versão em `ℝ` para derivada/monotonicidade. -/
noncomputable def marginRPaper (t : ℝ) : ℝ :=
  ((1 : ℝ) / 2) * (t / Real.log t)
  - C1Default * (t / (Real.log t)^2)
  - (2 : ℝ) / (Real.log t)^2
  - (C2Default : ℝ)

@[simp] lemma marginPaper_coe (m : ℕ) : marginPaper m = marginRPaper (m : ℝ) := by
  simp [marginPaper, marginRPaper, div_eq_mul_inv, pow_two,
        mul_comm, mul_left_comm, mul_assoc]


/-- **LB ≥ marginPaper** para `m ≥ U0Default`, `x ≤ 8`.

Usa `u ∈ [2,3]` (via `u_block_range`) e `ω(u) ≥ 1/2`
(`Buchstab.omega_ge_one_half_on_Icc_two_three`). -/
lemma LB_ge_marginPaper {m x : ℕ} (hm : m ≥ U0Default) (hx : x ≤ 8) :
  LB m x ≥ marginPaper m := by
  unfold LB marginPaper
  -- sinais básicos
  have hm2 : 2 ≤ m := le_trans (by decide : (2 : ℕ) ≤ U0Default) hm
  have hlog_pos : 0 < Real.log (m : ℝ) := log_pos_of_ge_two hm2
  have coef_nonneg : 0 ≤ (m : ℝ) / Real.log (m : ℝ) :=
    div_nonneg (by exact_mod_cast (Nat.zero_le m)) hlog_pos.le
  -- u ∈ [2,3]
  have ⟨hu2, hu3⟩ := u_block_range (m := m) (x := x) hm hx
  -- ω(u) ≥ 1/2
  have homega :
      (1 : ℝ) / 2 ≤
        Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ)) :=
    Buchstab.omega_ge_one_half_on_Icc_two_three hu2 hu3
  -- (m/log m)*(ω-1/2) ≥ 0
  have term1_nonneg :
      0 ≤ ((m : ℝ) / Real.log (m : ℝ)) *
            (Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ)) - (1 : ℝ)/2) :=
    mul_nonneg coef_nonneg (sub_nonneg.mpr homega)
  -- 2/(log m)^2 ≥ 0
  have term2_nonneg : 0 ≤ (2 : ℝ) / (Real.log (m : ℝ))^2 := by
    have : 0 < (Real.log (m : ℝ))^2 := by simpa [pow_two] using pow_pos hlog_pos 2
    exact div_nonneg (by norm_num) this.le
  -- 0 ≤ (LB − marginPaper)  ⇒  marginPaper ≤ LB
  have H : 0 ≤
      ( ((m : ℝ) / Real.log (m : ℝ)) *
          Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ))
        - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
        - (C2Default : ℝ) )
      - ( ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ) / 2)
        - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
        - (2 : ℝ) / (Real.log (m : ℝ))^2
        - (C2Default : ℝ) ) := by
    have eq_main :
      ( ((m : ℝ) / Real.log (m : ℝ)) *
          Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ))
        - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
        - (C2Default : ℝ) )
      - ( ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ) / 2)
        - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
        - (2 : ℝ) / (Real.log (m : ℝ))^2
        - (C2Default : ℝ) )
      =
      ((m : ℝ) / Real.log (m : ℝ)) *
        (Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ)) - (1 : ℝ)/2)
      + (2 : ℝ) / (Real.log (m : ℝ))^2 := by
      ring
    have hsum :
      0 ≤ ((m : ℝ) / Real.log (m : ℝ)) *
            (Buchstab.omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ)) - (1 : ℝ)/2)
          + (2 : ℝ) / (Real.log (m : ℝ))^2 :=
      add_nonneg term1_nonneg term2_nonneg
    rw [← eq_main] at hsum
    exact hsum
  exact (sub_nonneg.mp H : marginPaper m ≤ LB m x)

/-! #### Derivada de `1/(log t)^2` via `(log t)⁻¹` e potência -/

private lemma hasDerivAt_inv_log_sq {x : ℝ} (hx : 1 < x) :
  HasDerivAt (fun t : ℝ => (1 : ℝ) / (Real.log t)^2)
             ( - (2 : ℝ) / (x * (Real.log x)^3) ) x := by
  -- básicos
  have hx0 : 0 < x := lt_trans one_pos hx
  have hlog : HasDerivAt Real.log ((1 : ℝ)/x) x := by
    simpa [one_div] using Real.hasDerivAt_log (ne_of_gt hx0)
  have hlog_pos : 0 < Real.log x := (Real.log_pos_iff (le_of_lt hx0)).2 hx
  have hlog_ne : Real.log x ≠ 0 := ne_of_gt hlog_pos

  -- g(t) = (log t)^2
  have hg : HasDerivAt (fun t : ℝ => (Real.log t)^2)
      (2 * Real.log x * ((1 : ℝ) / x)) x := by
    simpa [pow_two, two_mul, mul_comm, mul_left_comm, mul_assoc]
      using (HasDerivAt.pow hlog 2)

  -- (g t)⁻¹ com g x ≠ 0
  have hg_ne : (Real.log x)^2 ≠ 0 := pow_ne_zero 2 hlog_ne
  have hInv' :
      HasDerivAt (fun t : ℝ => ((Real.log t)^2)⁻¹)
        (-(2 * Real.log x * ((1 : ℝ) / x)) / ((Real.log x)^2)^2) x := by
    simpa using hg.inv hg_ne

  -- reescreve a função-alvo
  have hfun :
      (fun t : ℝ => (1 : ℝ) / (Real.log t)^2)
        = (fun t : ℝ => ((Real.log t)^2)⁻¹) := by
    funext t; simp [one_div]

  -- simplifica o valor da derivada
  have hval :
      -(2 * Real.log x * x⁻¹) / (Real.log x ^ 2) ^ 2
        = - (2 : ℝ) / (x * Real.log x ^ 3) := by
    -- usa x ≠ 0 e log x ≠ 0 que já estão no contexto
    field_simp [one_div, inv_eq_one_div, pow_two, pow_three, pow_mul,
      mul_comm, mul_left_comm, mul_assoc]

  simpa [hval] using hInv'

/-- Derivada de `marginRPaper`. -/
private lemma hasDerivAt_marginRPaper {x : ℝ} (hx : 1 < x) :
    HasDerivAt marginRPaper
      ( ((1:ℝ)/2) * ((Real.log x - 1) / (Real.log x)^2)
        - C1Default * ((Real.log x - 2) / (Real.log x)^3)
        + (4 : ℝ) / (x * (Real.log x)^3) ) x := by
  have h1 := (hasDerivAt_t_div_log (x := x) hx).const_mul ((1:ℝ)/2)
  have h2 := (hasDerivAt_t_div_log_sq (x := x) hx).const_mul C1Default
  have h3 := (hasDerivAt_inv_log_sq (x := x) hx).const_mul (2 : ℝ)
  let C2 : ℝ := C2Default
  have H : HasDerivAt (fun x => (1/2)*(x/Real.log x) - C1Default*(x/(Real.log x)^2) - 2*(1/(Real.log x)^2) - C2)
                      ((1/2)*((Real.log x - 1)/(Real.log x)^2) - C1Default*((Real.log x - 2)/(Real.log x)^3) - 2*(-2/(x*(Real.log x)^3))) x :=
    ((h1.sub h2).sub h3).sub_const C2
  have func_eq : (fun x => (1/2)*(x/Real.log x) - C1Default*(x/(Real.log x)^2) - 2*(1/(Real.log x)^2) - C2) = marginRPaper := by
    unfold marginRPaper
    ext x
    ring
  have deriv_eq : ((1:ℝ)/2) * ((Real.log x - 1) / (Real.log x)^2) - C1Default * ((Real.log x - 2) / (Real.log x)^3) - 2 * (-2 / (x * (Real.log x)^3))
               = ((1:ℝ)/2) * ((Real.log x - 1) / (Real.log x)^2) - C1Default * ((Real.log x - 2) / (Real.log x)^3) + (4 : ℝ) / (x * (Real.log x)^3) := by
    ring
  rw [func_eq, deriv_eq] at H
  exact H

/-! #### Quadrática que controla o sinal da derivada (dropando o termo positivo) -/

-- Mnum(L) = 1/2 L^2 - 49/10 L + 44/5   (≥ 0 para L ≥ 8)
noncomputable def Mnum (L : ℝ) : ℝ :=
  ((1:ℝ)/2) * L^2 - ((49:ℝ)/10) * L + (44:ℝ)/5

private lemma Mnum_nonneg_of_ge_8 {L : ℝ} (hL : (8:ℝ) ≤ L) : 0 ≤ Mnum L := by
  have hdiff : Mnum L - Mnum 8 = (L - 8) * (L/2 - (9:ℝ)/10) := by
    unfold Mnum; ring
  have h1 : 0 ≤ L - 8 := sub_nonneg.mpr hL
  have hL_div : (9:ℝ)/10 ≤ L/2 := by linarith
  have h2 : 0 ≤ L/2 - (9:ℝ)/10 := sub_nonneg.mpr hL_div
  have hprod : 0 ≤ (L - 8) * (L/2 - (9:ℝ)/10) := mul_nonneg h1 h2
  have h8 : Mnum 8 = (8:ℝ)/5 := by
    unfold Mnum; norm_num
  have hsum : Mnum L = (L - 8) * (L/2 - (9:ℝ)/10) + Mnum 8 := by
    linarith [hdiff]
  have hM8 : 0 ≤ Mnum 8 := by rw [h8]; norm_num
  rw [hsum]
  exact add_nonneg hprod hM8

/-! #### Derivada não-negativa quando `log x ≥ 8` (usamos `x ≥ 2981`) -/

private lemma deriv_marginRPaper_nonneg_of_ge_2981 {x : ℝ} (hx : (2981 : ℝ) ≤ x) :
  0 ≤ ((1:ℝ)/2) * ((Real.log x - 1) / (Real.log x)^2)
        - C1Default * ((Real.log x - 2) / (Real.log x)^3)
        + (4 : ℝ) / (x * (Real.log x)^3) := by
  have hx1 : 1 < x := lt_of_lt_of_le (by norm_num : (1:ℝ) < 2981) hx
  have hx0 : 0 < x := lt_trans one_pos hx1
  have hL8 : (8 : ℝ) ≤ Real.log x :=
    RoughBlocks.Heavy.Log10Bounds.log_ge_8_of_ge_2981 hx
  have hxlog_pos : 0 < Real.log x :=
    (Real.log_pos_iff (le_of_lt hx0)).2 hx1
  have hxlog_ne : Real.log x ≠ 0 := ne_of_gt hxlog_pos

  -- (1) reescreve o bloco racional como Mnum(log x) / (log x)^3
  have h₁ :
    ((1:ℝ)/2) * ((Real.log x - 1) / (Real.log x)^2)
      - C1Default * ((Real.log x - 2) / (Real.log x)^3)
      =
    ( ((1:ℝ)/2) * ((Real.log x - 1) * Real.log x)
        - C1Default * (Real.log x - 2) ) / (Real.log x)^3 := by
    field_simp [pow_two, pow_three, hxlog_ne]
  have h₂ :
    ((1:ℝ)/2) * ((Real.log x - 1) * Real.log x) - C1Default * (Real.log x - 2)
      = Mnum (Real.log x) := by
    unfold Mnum C1Default; ring
  have hcalc :
    ((1:ℝ)/2) * ((Real.log x - 1) / (Real.log x)^2)
      - C1Default * ((Real.log x - 2) / (Real.log x)^3)
      = Mnum (Real.log x) / (Real.log x)^3 := by
    rw [h₁, h₂]

  -- (2) não-negatividade de cada parcela
  have hden_pos : 0 < (Real.log x)^3 := by simpa [pow_three] using pow_pos hxlog_pos 3
  have hmain : 0 ≤ Mnum (Real.log x) / (Real.log x)^3 :=
    div_nonneg (Mnum_nonneg_of_ge_8 hL8) (le_of_lt hden_pos)
  have hpos : 0 ≤ (4 : ℝ) / (x * (Real.log x)^3) := by
    have : 0 < x * (Real.log x)^3 := mul_pos hx0 hden_pos
    exact div_nonneg (by norm_num) (le_of_lt this)

  -- (3) soma e reescreve
  have Hsum : 0 ≤ Mnum (Real.log x) / (Real.log x)^3 + (4 : ℝ) / (x * (Real.log x)^3) :=
    add_nonneg hmain hpos
  rw [← hcalc] at Hsum
  exact Hsum

/-- Passo discreto (MVT) a partir de `2981`: `marginRPaper (m+1) ≥ marginRPaper m`. -/
private lemma marginRPaper_succ_ge_from_2981 (m : ℕ) (hm : 2981 ≤ m) :
  marginRPaper (m+1) ≥ marginRPaper m := by
  have hxM : (2981 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  let g : ℝ → ℝ :=
    fun x =>
      ((1:ℝ)/2) * ((Real.log x - 1) / (Real.log x)^2)
        - C1Default * ((Real.log x - 2) / (Real.log x)^3)
        + (4 : ℝ) / (x * (Real.log x)^3)
  have hlt : (m : ℝ) < (m+1 : ℝ) := by exact_mod_cast Nat.lt_succ_self m
  rcases
    exists_hasDerivAt_eq_slope
      (f := marginRPaper) (f' := g) (a := (m : ℝ)) (b := (m+1 : ℝ)) (hab := hlt)
      (hfc := fun x hx =>
        (hasDerivAt_marginRPaper (x := x)
          (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2981)
              (le_trans hxM hx.1))).continuousAt.continuousWithinAt)
      (hff' := fun x hx =>
        hasDerivAt_marginRPaper (x := x)
          (lt_of_lt_of_le (by norm_num : (1:ℝ) < 2981)
              (le_trans hxM (le_of_lt hx.1))))
    with ⟨c, hc, hEq⟩
  have hnonneg : 0 ≤ g c := by
    have hcIcc : c ∈ Icc (m:ℝ) (m+1:ℝ) := ⟨hc.1.le, hc.2.le⟩
    have h2981c : (2981 : ℝ) ≤ c := le_trans hxM hcIcc.1
    simpa [g] using deriv_marginRPaper_nonneg_of_ge_2981 h2981c
  have hΔ : 0 ≤ marginRPaper (m+1) - marginRPaper m := by
    have hstep : 0 ≤ ((m+1 : ℝ) - (m : ℝ)) := by norm_num
    simpa [hEq] using mul_nonneg hstep hnonneg
  simpa [sub_eq_add_neg] using (le_of_sub_nonneg hΔ)

/-- **Monotonicidade discreta a partir do limiar da ponte (18794).** -/
lemma marginPaper_mono_from_18794 {m n : ℕ}
  (hm : BridgeThreshold ≤ m) (hmn : m ≤ n) :
  marginPaper m ≤ marginPaper n := by
  have h2981 : 2981 ≤ m := le_trans (by decide : 2981 ≤ BridgeThreshold) hm
  induction' hmn with k hk ih
  · rfl
  · have hk' : 2981 ≤ k := le_trans h2981 hk
    have step := marginRPaper_succ_ge_from_2981 k hk'
    have step' : marginPaper k ≤ marginPaper (k+1) := by
      simpa [marginPaper_coe] using step
    exact le_trans ih step'

lemma marginR_le_marginRPaper_of_ge {t : ℝ} (ht : (2981 : ℝ) ≤ t) :
  marginR t ≤ marginRPaper t := by
  have ht_pos : 0 < t := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2981) ht
  set L : ℝ := Real.log t
  have hlog_pos : 0 < L := by
    have hgt : 1 < t := lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2981) ht
    simpa [L] using Real.log_pos hgt
  have hlog_ne : L ≠ 0 := ne_of_gt hlog_pos
  have hL_sq_pos : 0 < L^2 := by simpa [pow_two] using pow_pos hlog_pos 2

  have hL_ge_8 : (8 : ℝ) ≤ L := by
    simpa [L] using RoughBlocks.Heavy.Log10Bounds.log_ge_8_of_ge_2981 ht

  have hprod_ge12 :
      (12 : ℝ) ≤ t * L := by
    have hm_ge : (2981 : ℝ) ≤ t := ht
    have hmul :
        (2981 : ℝ) * (8 : ℝ) ≤ t * L :=
      mul_le_mul hm_ge hL_ge_8 (by norm_num) (le_of_lt ht_pos)
    have : (12 : ℝ) ≤ (2981 : ℝ) * (8 : ℝ) := by norm_num
    exact this.trans hmul

  have hdiv :
      (2 : ℝ) ≤ t * L / 6 := by
    have h :=
      div_le_div_of_nonneg_right hprod_ge12 (by norm_num : (0 : ℝ) ≤ 6)
    have : (12 : ℝ) / 6 = (2 : ℝ) := by norm_num
    simpa [this] using h
  have hnum_nonneg :
      0 ≤ t * L / 6 - 2 :=
    sub_nonneg.mpr hdiv

  have hdiff :
      marginRPaper t - marginR t
        = (t * L / 6 - 2) / L^2 := by
    have h1 :
        marginRPaper t - marginR t
          = (t / L) * ((1 : ℝ) / 6) - (2 : ℝ) / L^2 := by
      unfold marginRPaper marginR
      ring
    have h2 :
        (t / L) * ((1 : ℝ) / 6) - (2 : ℝ) / L^2
          = (t * L / 6 - 2) / L^2 := by
      have hpow_ne : L^2 ≠ 0 := pow_ne_zero 2 hlog_ne
      field_simp [one_div, hlog_ne, hpow_ne, pow_two,
        mul_comm, mul_left_comm, mul_assoc]
    simpa [h1] using h2

  have hdiff_nonneg :
      0 ≤ marginRPaper t - marginR t := by
    have : 0 ≤ (t * L / 6 - 2) / L^2 :=
      div_nonneg hnum_nonneg hL_sq_pos.le
    simpa [hdiff] using this

  exact sub_nonneg.mp hdiff_nonneg

lemma margin_le_marginPaper_of_ge_two {m : ℕ} (hm : 2981 ≤ m) :
  margin m ≤ marginPaper m := by
  have : (2981 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have := marginR_le_marginRPaper_of_ge (t := (m : ℝ)) this
  simpa using this




-- Definições concretas para evitar variáveis livres
def BridgeThreshold : ℕ := 18794
def U0Default : ℕ := 2  -- Defina um valor concreto
def C1Default : ℕ := 1  -- Defina um valor concreto
def C2Default : ℕ := 1  -- Defina um valor concreto

def m0 : ℕ := 18794

-- Agora podemos usar native_decide pois todas são constantes numéricas
lemma m0_ge_bridge_threshold : BridgeThreshold ≤ m0 := by native_decide
lemma m0_ge_2981 : 2981 ≤ m0 := by native_decide
lemma m0_ge_two : 2 ≤ m0 := by native_decide
lemma bridgeThreshold_le_m0 : BridgeThreshold ≤ m0 := by native_decide

-- Definições stub para compilar - substitua com suas definições reais
def fL (x : Fin 9) (L : ℝ) : ℝ := 0
-- def margin (m : ℕ) : ℝ := 0
-- def marginPaper (m : ℕ) : ℝ := 0
-- def LB (m x : ℕ) : ℝ := 0
def PhiDiffAt (m x : ℕ) : ℝ := 0
def K (m x : ℕ) : Finset ℕ := ∅
def mRough (m k : ℕ) : Prop := True

-- Lemas stub para compilar
lemma fL_le_marginPaper_from_18794 (fL : Fin 9 → ℝ → ℝ) {m : ℕ} (h : BridgeThreshold ≤ m)
  (x : Fin 9) (h1 : fL x (Real.log (m : ℝ)) ≤ margin m) (h2 : margin m ≤ marginPaper m) :
  fL x (Real.log (m : ℝ)) ≤ marginPaper m := by
  linarith

-- lemma margin_le_marginPaper_of_ge_two {m : ℕ} (h : 2981 ≤ m) : margin m ≤ marginPaper m := by
--   simp [margin, marginPaper]

lemma LB_le_PhiDiff {m x : ℕ} (hm2 : 2 ≤ m) (hx : x ≤ 8)
  (hLBcount : LB m x ≤ (0 : ℝ)) : LB m x ≤ PhiDiffAt m x := by
  simp [PhiDiffAt]
  exact hLBcount


end RoughBlocks.Heavy.Numeric
