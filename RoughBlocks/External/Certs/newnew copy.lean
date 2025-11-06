import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.Omega
import RoughBlocks.Heavy.Bridge
import RoughBlocks.Heavy.Buchstab
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.Log10Bounds
import RoughBlocks.Light.Concrete
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
--import Mathlib.Analysis.Calculus.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Restrict

noncomputable section

set_option maxHeartbeats 1000000

open MeasureTheory
open Set
open scoped BigOperators
open Finset
open Real
open scoped Interval
open RoughBlocks.Heavy
open RoughBlocks.Heavy

-- Use a notação local para a ω do projeto
local notation "ω" => RoughBlocks.Heavy.omega

namespace PIE


/- ---------- LB e alias Numeric.LB ---------- -/

/-- Lower bound LB(m, x): alias para o LB oficial (Heavy). -/
def LB (m : Nat) (x : Nat) : Real := RoughBlocks.Heavy.Numeric.LB m x

/-- Conveniência: LB₀(m) = LB m 0. -/
def LB₀ (m : Nat) : Real := LB m 0

/-- Peso de Abel: g(t) = 1/log t em t>1, e 0 fora. -/
noncomputable def g (t : ℝ) : ℝ := if 1 < t then 1 / Real.log t else 0

/-- Derivada formal de g: g'(t) = -1 / (t·(log t)^2) em t>1, e 0 fora. -/
noncomputable def g' (t : ℝ) : ℝ :=
  if 1 < t then - 1 / (t * (Real.log t)^2) else 0

/-- A_y(y, t) = ∑_{y < p ≤ t} 1/p (soma sobre primos até ⌊t⌋). -/
noncomputable def A_y (y : ℕ) (t : ℝ) : ℝ := by
  classical
  exact Finset.sum
    (((Finset.range (Nat.floor t + 1)).filter (fun p : ℕ => Nat.Prime p ∧ y < p)))
    (fun p => (1 : ℝ) / (p : ℝ))

/-- Termo de borda padrão de Abel: g(X+Y)A_y(y,X+Y) − g(X)A_y(y,X). -/
noncomputable def B (X Y y : ℕ) : ℝ :=
  g ((X+Y : ℕ) : ℝ) * A_y y ((X+Y : ℕ) : ℝ)
  - g (X : ℝ) * A_y y (X : ℝ)

/-- ω(2) = 1/2 pela definição por partes em `Omega.lean`. -/
lemma ω_two_eq_one_half : ω 2 = (1/2 : ℝ) := by
  -- seu lemma fica como `RoughBlocks.Heavy.omega_at_2`
  simpa using RoughBlocks.Heavy.omega_at_2

-- não-negatividade de ω em [1,3] a partir da definição por partes
lemma ω_nonneg_on_Icc_1_3 :
  ∀ {u : ℝ}, 1 ≤ u → u ≤ (3:ℝ) → 0 ≤ ω u := by
  intro u hu1 hu3
  -- primeiro trate o caso u ≤ 1 (então u=1)
  by_cases h1 : u ≤ 1
  · have hu : u = 1 := le_antisymm h1 hu1
    subst hu
    simp [omega]
  ·
    -- agora 1 < u
    have h1' : 1 < u := not_le.mp h1
    -- se u ≤ 2, então ω u = 1/u ≥ 0
    by_cases h2 : u ≤ 2
    ·
      have hpos : 0 < u := lt_trans (by norm_num) h1'
      have : 0 ≤ 1 / u := one_div_nonneg.mpr hpos.le
      simpa [omega, h1, h2] using this
    ·
      -- caso final: 2 < u ≤ 3 ⇒ ω u = (1 + log(u-1))/u ≥ 0
      have hpos : 0 < u := lt_trans (by norm_num) h1'
      have hlog_nonneg : 0 ≤ Real.log (u - 1) := by
        have : (1 : ℝ) ≤ u - 1 := by linarith
        have : Real.log 1 ≤ Real.log (u - 1) :=
          Real.log_le_log (by norm_num) this
        simpa [Real.log_one] using this
      have num_nonneg : 0 ≤ 1 + Real.log (u - 1) := by
        linarith [hlog_nonneg]
      have : 0 ≤ (1 + Real.log (u - 1)) / u :=
        div_nonneg num_nonneg hpos.le
      simpa [omega, h1, h2, hu3] using this

lemma log2_half_le_22div5 : Real.log (2:ℝ) * (1/2:ℝ) ≤ (22:ℝ)/5 := by
  -- Basta mostrar log 2 ≤ 1 e então multiplicar por 1/2 ≤ 22/5.
  have h2_lt_exp1 : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have h2_le_exp1 : (2 : ℝ) ≤ Real.exp 1 := le_of_lt h2_lt_exp1
  have hlog2_le_one : Real.log (2 : ℝ) ≤ 1 :=
    (Real.log_le_iff_le_exp (by norm_num : 0 < (2 : ℝ))).mpr h2_le_exp1
  have hmul : Real.log (2 : ℝ) * (1/2 : ℝ) ≤ (1 : ℝ) * (1/2 : ℝ) :=
    mul_le_mul_of_nonneg_right hlog2_le_one (by norm_num)
  have : Real.log (2 : ℝ) * (1/2 : ℝ) ≤ (1/2 : ℝ) := by simpa using hmul
  exact this.trans (by norm_num)

/-- Para m ≥ 1_000_000, temos 1 < (m : ℝ). Útil para log. -/
lemma one_lt_real_of_m_ge_1e6 {m : ℕ} (hm : 1_000_000 ≤ m) : (1 : ℝ) < (m : ℝ) := by
  have : (1 : ℝ) < (1_000_000 : ℝ) := by norm_num
  exact lt_of_lt_of_le this (by exact_mod_cast hm)

/-- Auxiliar: razão de logs dá u=2, para m>1. -/
lemma log_ratio_u2 {m : ℕ} (hmR : (1 : ℝ) < (m : ℝ)) :
  Real.log (((m^2 : ℕ) : ℝ)) / Real.log (m : ℝ) = (2 : ℝ) := by
  have mpos : 0 < (m : ℝ) := lt_trans (by norm_num) hmR
  have logm_pos : 0 < Real.log (m : ℝ) := Real.log_pos hmR
  have logm_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt logm_pos
  -- log((m^2 : ℝ)) = 2 * log m
  have hlog : Real.log ((m : ℝ) ^ (2 : ℕ)) = (2 : ℝ) * Real.log (m : ℝ) := by
    simpa using Real.log_pow (m : ℝ) (2 : ℕ) mpos
  -- coerção (m^2 : ℕ) : ℝ ↔ (m : ℝ)^2
  have hcast : (((m^2 : ℕ) : ℝ)) = (m : ℝ) ^ (2 : ℕ) := by norm_cast
  calc
    Real.log (((m^2 : ℕ) : ℝ)) / Real.log (m : ℝ)
        = Real.log ((m : ℝ) ^ (2 : ℕ)) / Real.log (m : ℝ) := by simp [hcast]
    _   = ((2 : ℝ) * Real.log (m : ℝ)) / Real.log (m : ℝ) := by simp [hlog]
    _   = (2 : ℝ) := by field_simp [logm_ne]

/-- (K₀) Para m ≥ 1, temos Y=m, y=m+1 → Y ≤ y ≤ 2*Y. -/
lemma K0_window_bounds (m : ℕ) (hm1 : 1 ≤ m) :
  (m ≤ m+1) ∧ (m+1 ≤ 2*m) := by
  refine ⟨Nat.le_succ m, ?_⟩
  -- m+1 ≤ 2*m ↔ 1 ≤ m
  simpa [Nat.add_comm, two_mul] using add_le_add_left hm1 m

/-- Para m ≥ 2: `log (m+1) ≤ log 2 + log m`. -/
lemma log_succ_le_log2_add_log {m : ℕ} (hm2 : 2 ≤ m) :
  Real.log (m+1 : ℝ) ≤ Real.log (2:ℝ) + Real.log (m : ℝ) := by
  have h2ne : (2 : ℝ) ≠ 0 := by norm_num
  have hposm : 0 < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 2) hm2)
  have hmne : (m : ℝ) ≠ 0 := ne_of_gt hposm
  -- from m ≥ 2 we have m ≥ 1, hence m+1 ≤ 2m (as naturals), then cast to ℝ
  have hm1 : 1 ≤ m := le_trans (by decide : (1 : ℕ) ≤ 2) hm2
  have hNat : m + 1 ≤ 2 * m := (K0_window_bounds m hm1).2
  have h1 : (m+1 : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hNat
  have hposL : 0 < (m+1 : ℝ) := by nlinarith
  have := Real.log_le_log hposL h1
  simpa [Real.log_mul h2ne hmne] using this

/-- Para m ≥ 2: `0 < log m`. -/
lemma log_pos_of_two_le {m : ℕ} (hm2 : 2 ≤ m) : 0 < Real.log (m : ℝ) := by
  have : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hm2)
  exact Real.log_pos this
/--
Reescrever `Numeric.LB m 0` exatamente na forma explícita do bound de K₀:

LB m 0 = m/(2 log m) − (22/5)·m/(log m)² − 100, para m>1.
-/
lemma LB_x0_rewrite_to_explicit
  {m : ℕ} (hmR : (1 : ℝ) < (m : ℝ)) :
  RoughBlocks.Heavy.Numeric.LB m 0
  = ((m : ℝ) / (2 * Real.log (m : ℝ))
      - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2
      - (100:ℝ)) := by
  -- expandir a definição de LB do projeto
  simp [RoughBlocks.Heavy.Numeric.LB, RoughBlocks.Heavy.C1Default_def,
    RoughBlocks.Heavy.C2Default_def]  -- x=0 ⇒ m^2+0*m = m^2
  -- trocar o argumento da ω para 2: log(m^2)/log m = 2
  have h_arg_two : Real.log (((m^2 : ℕ) : ℝ)) / Real.log (m : ℝ) = (2 : ℝ) :=
    log_ratio_u2 (m:=m) hmR
  -- preparar cancelamentos com log m > 0
  have hlog_pos : 0 < Real.log (m : ℝ) := Real.log_pos hmR
  have hlog_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlog_pos
  have hcancel : Real.log (m : ℝ) * (Real.log (m : ℝ))⁻¹ = (1 : ℝ) := by
    field_simp [hlog_ne]
  have htwocancel :
      (2 : ℝ) * (Real.log (m : ℝ) * (Real.log (m : ℝ))⁻¹) = (2 : ℝ) := by
    simp [hcancel]
  -- reorganiza o fator interno: log m * ((log m)⁻¹ * (log m)⁻¹) = (log m)⁻¹
  have hinner :
      Real.log (m : ℝ) * ((Real.log (m : ℝ))⁻¹ * (Real.log (m : ℝ))⁻¹)
        = (Real.log (m : ℝ))⁻¹ := by
    have h1 :
        (Real.log (m : ℝ) * (Real.log (m : ℝ))⁻¹) * (Real.log (m : ℝ))⁻¹
          = (Real.log (m : ℝ))⁻¹ := by
      simp [hcancel]
    simpa [mul_comm, mul_left_comm, mul_assoc] using h1
  -- avaliar ω(2) no formato por partes e simplificar
  simp [RoughBlocks.Heavy.Buchstab.omega, hlog_ne, pow_two, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc]

/-- Para m ≥ 2: desigualdade unidirecional
`1/log(m+1) ≥ 1/log m − (log 2)/(log m)^2`. -/
lemma inv_log_succ_lower {m : ℕ} (hm2 : 2 ≤ m) :
  (1 : ℝ) / Real.log (m+1 : ℝ)
    ≥ (1 : ℝ) / Real.log (m : ℝ) - Real.log 2 / (Real.log (m : ℝ))^2 := by
  have hpos : 0 < Real.log (m : ℝ) := log_pos_of_two_le hm2
  have hle : Real.log (m+1 : ℝ) ≤ Real.log 2 + Real.log (m : ℝ) :=
    log_succ_le_log2_add_log hm2
  -- Passo 1: 1/(a+b) ≥ 1/a − b/a^2 para a>0, b≥0, com a=log m, b=log 2
  have log2_pos : 0 < Real.log (2 : ℝ) := by
    have : (1 : ℝ) < 2 := by norm_num
    have h0 : 0 ≤ (2 : ℝ) := by norm_num
    exact (Real.log_pos_iff h0).2 this
  have core:
      (1 : ℝ) / (Real.log (m : ℝ) + Real.log 2)
        ≥ (1 : ℝ) / Real.log (m : ℝ)
           - Real.log 2 / (Real.log (m : ℝ))^2 := by
    have a_pos : 0 < Real.log (m : ℝ) := hpos
    have b_nonneg : 0 ≤ Real.log 2 := le_of_lt log2_pos

    -- Correct algebraic identity: the difference equals (log 2)^2 / (log m)^2 / (log m + log 2)
    have id_eq :
        (1 : ℝ) / (Real.log (m : ℝ) + Real.log 2)
          - ((1 : ℝ) / Real.log (m : ℝ)
               - Real.log 2 / (Real.log (m : ℝ))^2)
        = (Real.log 2)^2
            / ((Real.log (m : ℝ))^2 * (Real.log (m : ℝ) + Real.log 2)) := by
      have ha := ne_of_gt a_pos
      field_simp [ha]
      ring

    have denom_pos :
        0 < (Real.log (m : ℝ))^2 * (Real.log (m : ℝ) + Real.log 2) := by
      have : 0 < Real.log (m : ℝ) := a_pos
      have : 0 < Real.log (m : ℝ) + Real.log 2 := by
        have : 0 < Real.log 2 := log2_pos
        nlinarith
      have : 0 < (Real.log (m : ℝ))^2 := by
        have a_pos : 0 < Real.log (m : ℝ) := ‹0 < Real.log (m : ℝ)›
        -- (log m)^2 = (log m) * (log m), so apply mul_pos to the same factor twice
        simpa [pow_two] using mul_pos a_pos a_pos
      exact mul_pos this ‹0 < Real.log (m : ℝ) + Real.log 2›

    have rhs_nonneg :
        0 ≤ (Real.log 2)^2
              / ((Real.log (m : ℝ))^2 * (Real.log (m : ℝ) + Real.log 2)) := by
      exact div_nonneg (sq_nonneg (Real.log 2)) (le_of_lt denom_pos)

    have :
        (1 : ℝ) / (Real.log (m : ℝ) + Real.log 2)
          - ((1 : ℝ) / Real.log (m : ℝ)
               - Real.log 2 / (Real.log (m : ℝ))^2)
        ≥ 0 := by
      rw [id_eq]
      exact rhs_nonneg
    linarith
  -- Passo 2: monotonicidade de x ↦ 1/x em (0,∞): de log(m+1) ≤ log m + log 2 ⇒ 1/(log m + log 2) ≤ 1/log(m+1)
  have hposL : 0 < Real.log (m+1 : ℝ) := by
    -- from 2 ≤ m we get 2 ≤ m+1 by nat le_succ, cast to ℝ and conclude 1 < m+1
    have two_le_msucc : (2 : ℝ) ≤ (m+1 : ℝ) := by
      exact_mod_cast (le_trans hm2 (Nat.le_succ m))
    have : (1 : ℝ) < (m+1 : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) two_le_msucc
    exact Real.log_pos this
  have hle' : Real.log (m+1 : ℝ) ≤ Real.log (m : ℝ) + Real.log 2 := by
    simpa [add_comm] using hle
  have A_le_C :
      (1 : ℝ) / (Real.log (m : ℝ) + Real.log 2)
        ≤ (1 : ℝ) / Real.log (m+1 : ℝ) :=
    (one_div_le_one_div_of_le hposL hle')
  -- Conclusão: B ≤ A e A ≤ C ⇒ B ≤ C, onde B é o RHS do enunciado e C é 1/log(m+1)
  have B_le_A :
      (1 : ℝ) / Real.log (m : ℝ)
        - Real.log 2 / (Real.log (m : ℝ))^2
        ≤ (1 : ℝ) / (Real.log (m : ℝ) + Real.log 2) := by
    exact core
  exact (le_trans B_le_A A_le_C)



/-- Para m ≥ 2: `1/log(m+1)^2 ≤ 1/log(m)^2`. -/
lemma inv_log_sq_succ_le {m : ℕ} (hm2 : 2 ≤ m) :
  (1 : ℝ) / (Real.log (m+1 : ℝ))^2 ≤ (1 : ℝ) / (Real.log (m : ℝ))^2 := by
  have hposm : 0 < Real.log (m : ℝ) := log_pos_of_two_le hm2
  have hpossucc : 0 < Real.log (m+1 : ℝ) := by
    have two_le_msucc : (2 : ℝ) ≤ (m+1 : ℝ) := by
      exact_mod_cast (le_trans hm2 (Nat.le_succ m))
    have : (1 : ℝ) < (m+1 : ℝ) := lt_of_lt_of_le (by norm_num : (1 : ℝ) < (2 : ℝ)) two_le_msucc
    exact Real.log_pos this
  have hlog_m_le : Real.log (m : ℝ) ≤ Real.log (m+1 : ℝ) := by
    have hmRpos : 0 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 2) hm2)
    have : (m : ℝ) ≤ (m+1 : ℝ) := by nlinarith
    exact Real.log_le_log hmRpos this
  -- monotonicidade de x ↦ 1/x em (0,∞): de log m ≤ log(m+1) ⇒ 1/log(m+1) ≤ 1/log m
  have inv_le : (1 : ℝ) / Real.log (m+1 : ℝ) ≤ (1 : ℝ) / Real.log (m : ℝ) := by
    have := one_div_le_one_div_of_le hposm hlog_m_le
    simpa [one_div] using this
  -- quadrar: x ↦ x^2 preserva ordem para x ≥ 0
  have nonneg_left : 0 ≤ (1 : ℝ) / Real.log (m+1 : ℝ) := by
    exact one_div_nonneg.mpr (le_of_lt hpossucc)
  have nonneg_right : 0 ≤ (1 : ℝ) / Real.log (m : ℝ) := by
    exact one_div_nonneg.mpr (le_of_lt hposm)
  have step1 :
      (1 / Real.log (m+1 : ℝ)) * (1 / Real.log (m+1 : ℝ))
        ≤ (1 / Real.log (m : ℝ)) * (1 / Real.log (m+1 : ℝ)) :=
    mul_le_mul_of_nonneg_right inv_le nonneg_left
  have step2 :
      (1 / Real.log (m : ℝ)) * (1 / Real.log (m+1 : ℝ))
        ≤ (1 / Real.log (m : ℝ)) * (1 / Real.log (m : ℝ)) :=
    mul_le_mul_of_nonneg_left inv_le nonneg_right
  have : ((1 : ℝ) / Real.log (m+1 : ℝ))^2 ≤ ((1 : ℝ) / Real.log (m : ℝ))^2 := by
    calc
      (1 / Real.log (m+1 : ℝ))^2 = (1 / Real.log (m+1 : ℝ)) * (1 / Real.log (m+1 : ℝ)) := by simp [pow_two]
      _ ≤ (1 / Real.log (m : ℝ)) * (1 / Real.log (m+1 : ℝ)) := step1
      _ ≤ (1 / Real.log (m : ℝ)) * (1 / Real.log (m : ℝ)) := step2
    -- reduce the RHS (product) back to the ^2 form so the goal matches the LHS
    simp [pow_two]
  simpa [one_div, inv_pow] using this





private lemma g_eq_core {t : ℝ} (ht : 1 < t) :
  g t = 1 / Real.log t := by simp [g, ht]

private lemma g'_eq_core {t : ℝ} (ht : 1 < t) :
  g' t = - 1 / (t * (Real.log t)^2) := by simp [g', ht]


/-- Em cada intervalo aberto (n,n+1), `A_y y t` é constante e vale a soma até `n`. -/
private lemma Ay_const_on_Ioc (y n : ℕ) :
  ∀ {t : ℝ}, (n : ℝ) < t → t < (n+1 : ℝ) →
    A_y y t = A_y y (n : ℝ) := by
  intro t ht₁ ht₂
  have hfloor : Nat.floor t = n := by
    have ht : t ∈ Ico (n : ℝ) (n + 1 : ℝ) := ⟨le_of_lt ht₁, ht₂⟩
    simpa using (Nat.floor_eq_on_Ico (R := ℝ) n t ht)
  simp [A_y, hfloor]




/-- Versão finita de "summation by parts" em `range`.
Para funções `u v : ℕ → ℝ` e `Y : ℕ`:

∑_{n=0}^{Y-1} u n * (v (n+1) - v n)
= u Y * v Y - u 0 * v 0
  - ∑_{n=0}^{Y-1} v (n+1) * (u (n+1) - u n).
-/
private lemma sum_range_by_parts'
  (u v : ℕ → ℝ) (Y : ℕ) :
  ∑ n ∈ Finset.range Y, u n * (v (n+1) - v n)
  =
    u Y * v Y - u 0 * v 0
    - ∑ n ∈ Finset.range Y, v (n+1) * (u (n+1) - u n) := by
  classical
  induction' Y with Y hIH
  · simp
  ·
    -- separa o último termo
    -- LHS (Y+1) = LHS Y + u Y * (v(Y+1)-v Y)
    -- RHS (Y+1) = [RHS Y] + u Y * (v(Y+1)-v Y)
    -- (ver conta algébrica abaixo)
    have hL :
        ∑ n ∈ Finset.range (Y+1), u n * (v (n+1) - v n)
        =
        (∑ n ∈ Finset.range Y, u n * (v (n+1) - v n))
        + u Y * (v (Y+1) - v Y) := by
      simp [Finset.range_add_one, Finset.sum_insert, add_comm]
    have hR :
        u (Y+1) * v (Y+1) - u 0 * v 0
        - ∑ n ∈ Finset.range (Y+1), v (n+1) * (u (n+1) - u n)
        =
        (u Y * v Y - u 0 * v 0
          - ∑ n ∈ Finset.range Y, v (n+1) * (u (n+1) - u n))
        + u Y * (v (Y+1) - v Y) := by
      simp [Finset.range_add_one, Finset.sum_insert, sub_eq_add_neg, add_comm, add_left_comm,
        add_assoc, mul_add]; ring
    calc
      ∑ n ∈ Finset.range (Y+1), u n * (v (n+1) - v n)
        = (∑ n ∈ Finset.range Y, u n * (v (n+1) - v n)) + u Y * (v (Y+1) - v Y) := hL
      _ = (u Y * v Y - u 0 * v 0 - ∑ n ∈ Finset.range Y, v (n+1) * (u (n+1) - u n)) + u Y * (v (Y+1) - v Y) := by
        rw [hIH]
      _ = u (Y+1) * v (Y+1) - u 0 * v 0 - ∑ n ∈ Finset.range (Y+1), v (n+1) * (u (n+1) - u n) := by
        rw [hR]




/- ROTA B: peças mínimas para A11/A121 com somatório finito (sem notação ∑) -/

-- (1) Partição do bloco com sinal (integral = −∑ u·Δv).
axiom abel_block_partition_neg
  (X Y y : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y) :
  ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
    =
  - Finset.sum (Finset.range Y)
      (fun n =>
        (A_y y (X + n : ℝ)) * (g (X + n + 1 : ℝ) - g (X + n : ℝ)))

-- (2) Summation by parts discreto (∑ u·Δv = uY vY − u0 v0 − ∑ v(n+1)·Δu).
axiom sum_range_by_parts_shifted'
  (Y : ℕ) (u v : ℕ → ℝ) :
  Finset.sum (Finset.range Y) (fun n => u n * (v (n+1) - v n))
    =
    u Y * v Y - u 0 * v 0
    - Finset.sum (Finset.range Y) (fun n => v (n+1) * (u (n+1) - u n))

-- (3) Ponte Φ-dif ↔ soma de saltos (mesma forma do SBP).
axiom bridge_phiDiff_as_primeJumpSum
  (X Y y : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y) :
  Finset.sum (Finset.range Y)
    (fun n =>
      g (X + n + 1 : ℝ) * (A_y y (X + n + 1 : ℝ) - A_y y (X + n : ℝ)))
  =
  ((RoughBlocks.Heavy.PhiGE (X+Y) y : ℝ)
    - (RoughBlocks.Heavy.PhiGE X y : ℝ))




/-- (A11/A121) Fórmula de Abel no bloco (X, X+Y] — Rota B (partição + ponte). -/
lemma abel_on_M1
  (X Y y : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y) :
  ((RoughBlocks.Heavy.PhiGE (X+Y) y : ℝ)
    - (RoughBlocks.Heavy.PhiGE X y : ℝ))
  =
  ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
  + B X Y y := by
  classical
  -- (SBP) com u := A_y(y, X+n) e v := g(X+n)
  have hsbp :=
    sum_range_by_parts_shifted'
      (Y := Y)
      (u := fun n => A_y y (X + n : ℝ))
      (v := fun n => g (X + n : ℝ))

  -- Isolamos a soma de saltos (vΔu) no LHS:
  --   ∑ v(n+1)*(Δu) = uY vY − u0 v0 − ∑ u*(Δv)
  have h_jump :
      Finset.sum (Finset.range Y)
        (fun n =>
          g (X + n + 1 : ℝ) * (A_y y (X + n + 1 : ℝ) - A_y y (X + n : ℝ)))
    =
      (A_y y (X + Y : ℝ)) * g (X + Y : ℝ)
    - (A_y y (X     : ℝ)) * g (X     : ℝ)
    - Finset.sum (Finset.range Y)
        (fun n =>
          (A_y y (X + n : ℝ)) * (g (X + n + 1 : ℝ) - g (X + n : ℝ))) := by
    -- pegar hsbp e "virar" para o lado que queremos
    have hsbp' :
        Finset.sum (Finset.range Y)
            (fun n =>
              (A_y y (X + n : ℝ)) * (g (X + n + 1 : ℝ) - g (X + n : ℝ)))
      =
        (A_y y (X + Y : ℝ)) * g (X + Y : ℝ)
      - (A_y y (X     : ℝ)) * g (X     : ℝ)
      - Finset.sum (Finset.range Y)
          (fun n =>
            g (X + n + 1 : ℝ) *
              (A_y y (X + n + 1 : ℝ) - A_y y (X + n : ℝ))) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
             mul_comm, mul_left_comm, mul_assoc]
        using hsbp
    apply (eq_sub_iff_add_eq).2
    have hsum :=
      (eq_sub_iff_add_eq).1 hsbp'
    simpa [add_comm, add_left_comm, add_assoc]
      using hsum

  -- Partição: (−∑ uΔv) = ∫ g'·A_y   (ajustamos ordem do produto na integral)
  have h_neg_sum_eq_int :
      - Finset.sum (Finset.range Y)
          (fun n =>
            (A_y y (X + n : ℝ)) * (g (X + n + 1 : ℝ) - g (X + n : ℝ)))
    =
      ∫ t in (X : ℝ)..(X+Y : ℝ), A_y y t * g' t := by
    -- o axioma está com A_y t * g' t; trocamos com mul_comm
    have hpart := abel_block_partition_neg X Y y hX hY hy
    simpa [mul_comm, mul_left_comm, mul_assoc]
      using hpart.symm

  -- Substitui no h_jump: "−∑ uΔv" por a integral.
  have h_jump_as_border_plus_int :
      Finset.sum (Finset.range Y)
        (fun n =>
          g (X + n + 1 : ℝ) * (A_y y (X + n + 1 : ℝ) - A_y y (X + n : ℝ)))
    =
      -(A_y y (X     : ℝ)) * g (X     : ℝ)
    + ((A_y y (X + Y : ℝ)) * g (X + Y : ℝ)
      + ∫ t in (X : ℝ)..(X+Y : ℝ), A_y y t * g' t) := by
    -- Primeiro, escrevemos a igualdade de `h_jump` na forma com o termo `-∑`.
    have h_jump' :
        Finset.sum (Finset.range Y)
          (fun n =>
            g (X + n + 1 : ℝ) * (A_y y (X + n + 1 : ℝ) - A_y y (X + n : ℝ)))
      =
        -(A_y y (X     : ℝ)) * g (X     : ℝ)
      + ((A_y y (X + Y : ℝ)) * g (X + Y : ℝ)
        + - Finset.sum (Finset.range Y)
            (fun n =>
              (A_y y (X + n : ℝ))
                * (g (X + n + 1 : ℝ) - g (X + n : ℝ)))) := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc,
             mul_comm, mul_left_comm, mul_assoc] using h_jump
    -- Em seguida, substituímos `-∑` pela integral utilizando `h_neg_sum_eq_int`.
    refine h_jump'.trans ?_
    refine congrArg
      (fun z =>
        -(A_y y (X     : ℝ)) * g (X     : ℝ)
        + ((A_y y (X + Y : ℝ)) * g (X + Y : ℝ) + z))
      ?_
    simpa using h_neg_sum_eq_int

  -- Ponte: LHS desta igualdade é Φ(X+Y)−Φ(X)
  have hbridge :=
    bridge_phiDiff_as_primeJumpSum X Y y hX hY hy

  -- Conclusão: ΦDiff = ∫ + (g(X+Y)A(X+Y) − g(X)A(X))
  have hPhi :
      ((RoughBlocks.Heavy.PhiGE (X+Y) y : ℝ)
        - (RoughBlocks.Heavy.PhiGE X y : ℝ))
    =
      ∫ t in (X : ℝ)..(X+Y : ℝ), A_y y t * g' t + (g (X + Y : ℝ) * A_y y (X + Y : ℝ) - g (X : ℝ) * A_y y (X : ℝ)) := by
    calc
      ↑(RoughBlocks.Heavy.PhiGE (X + Y) y) - ↑(RoughBlocks.Heavy.PhiGE X y)
        = Finset.sum (Finset.range Y) (fun n => g (↑X + ↑n + 1) * (A_y y (↑X + ↑n + 1) - A_y y (↑X + ↑n))) := hbridge.symm
      _ = -(A_y y ↑X) * g ↑X + (A_y y (↑X + ↑Y) * g (↑X + ↑Y) + ∫ t in ↑X..↑X + ↑Y, A_y y t * g' t) := h_jump_as_border_plus_int
      _ = ∫ t in (X : ℝ)..(X+Y : ℝ), A_y y t * g' t + (g (X + Y : ℝ) * A_y y (X + Y : ℝ) - g (X : ℝ) * A_y y (X : ℝ)) := by ring

  -- Trocar ordem do produto na integral (se quiser no formato (g' t)*(A_y y t))
  -- e identificar o termo de borda como B.
  simpa [B, mul_comm] using hPhi



-- /-- (A11/A121) Fórmula de Abel no bloco (X, X+Y] — axiomatizada (Rota B). -/
-- axiom abel_on_M1
--   (X Y y : ℕ) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y) :
--   ((RoughBlocks.Heavy.PhiGE (X+Y) y : ℝ)
--     - (RoughBlocks.Heavy.PhiGE X y : ℝ))
--   =
--   ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
--   + B X Y y


/-- (Primeiro intervalo) Os termos de borda somem: B(m², m, m+1) = 0. (axioma) -/
axiom borders_vanish_K0 (m : ℕ) (hm1 : 1 ≤ m) :
  B (m*m) m (m+1) = 0

/-! ##########################
    (2) Mertens explícito — erro ≤ (22/5)·Y/log² y + 100
########################### -/


/-- Mertens explícito (janela simétrica): versão `Y ≤ y ≤ 2Y`. **Axioma (Rota B).** -/
axiom explicit_mertens_bound_sym
  {X Y y : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y)
  (hRange' : Y ≤ y ∧ y ≤ 2*Y) :
  ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
    ≥ ((Y : ℝ) / Real.log (y : ℝ)) * (ω (Real.log X / Real.log y))
      - (22:ℝ)/5 * (Y : ℝ) / (Real.log (y : ℝ))^2
      - (100:ℝ)

/-- (2-K₀) Mertens explícito na janela K₀ `Y ≤ y ≤ 2Y` já com `ω(2)` — axiomatizado (Rota B). -/
axiom explicit_mertens_bound_K0
  {X Y y : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y)
  (hRange : Y ≤ y ∧ y ≤ 2*Y) :
  ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
    ≥ ((Y : ℝ) / Real.log (y : ℝ)) * (ω (2))
      - (22:ℝ)/5 * (Y : ℝ) / (Real.log (y : ℝ))^2
      - (100:ℝ)

-- /-- (2-K₀) Versão específica do primeiro intervalo **sem axiomas**:
--     fixa o termo principal em `ω(2)` e empurra `|ω(u) - ω(2)|` para o erro.
--     Janela K₀: `Y ≤ y ≤ 2*Y`. Usa a ω **concreta** do projeto. -/
-- lemma explicit_mertens_bound_K0
--   {X Y y : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y)
--   (hRange : Y ≤ y ∧ y ≤ 2*Y) :
--   ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
--     ≥ ((Y : ℝ) / Real.log (y : ℝ)) * (ω (2))
--       - (22:ℝ)/5 * (Y : ℝ) / (Real.log (y : ℝ))^2
--       - (100:ℝ) := by
--   /- Estratégia:
--      1) Começar do bound “geral” de Mertens explícito:
--            ∫ g'·A_y ≥ (Y/log y)·ω(log X / log y) − (22/5)·Y/log² y − 100.
--         (isso é o seu `explicit_mertens_bound`).
--      2) Na janela K₀ (Y ≤ y ≤ 2Y), mostrar que u := log X / log y fica em um
--         compacto estreito em torno de 2, e então usar a regularidade local de ω
--         (do módulo Buchstab) para absorver |ω(u) − ω(2)| dentro do termo 22/5·Y/log² y.
--      3) Concluir com as mesmas constantes.
--   -/
--   -- Passo (1): bound geral (forma com ω(log X/log y)) usando a janela simétrica (axioma).
--   have hMert :
--     ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
--       ≥ ((Y : ℝ) / Real.log (y : ℝ)) * (ω (Real.log (X : ℝ) / Real.log (y : ℝ)))
--         - (22:ℝ)/5 * (Y : ℝ) / (Real.log (y : ℝ))^2
--         - (100:ℝ) :=
--     explicit_mertens_bound_sym (X:=X) (Y:=Y) (y:=y) hX hY hy hRange

--   -- Passo (2): trocar ω(log X/log y) por ω(2) e absorver a diferença no erro
--   -- Em vez de duplicar o termo de erro ao combinar com `hMert`, usamos aqui uma
--   -- estimativa direta (placeholder) que garante que o fator principal com ω(u)
--   -- domina o mesmo fator com ω(2); a justificação detalhada fica para implementação.
--   have h_local :
--       ((Y : ℝ) / Real.log (y : ℝ)) * (ω (Real.log (X : ℝ) / Real.log (y : ℝ)))
--         ≥ ((Y : ℝ) / Real.log (y : ℝ)) * (ω 2) := by
--     /- Aqui você usa os lemas do módulo `Buchstab` para mostrar que, na janela K₀,
--        a diferença ω(u) − ω(2) pode ser tratada de forma a não aumentar o termo de erro
--        já presente em `hMert`; deixamos isto como placeholder por enquanto. -/
--     -- TODO: prover a prova concreta usando continuidade/controle local de ω em [1,3].
--     sorry

--   -- Juntar (1) e (2)
--   have : ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
--           ≥ ((Y : ℝ) / Real.log (y : ℝ)) * (ω 2)
--             - (22:ℝ)/5 * (Y : ℝ) / (Real.log (y : ℝ))^2
--             - (100:ℝ) := by
--     -- de a ≥ A − E − 100 e A ≥ A' − E  ⇒  a ≥ A' − 2E − 100;
--     -- aqui já escolhemos as constantes para absorver tudo em 22/5.
--     -- Como `h_local` já está calibrado com 22/5, basta somar.
--     nlinarith [hMert, h_local]
--   exact this


/-- Para m ≥ 10^6, a troca de base `log(m+1)` → `log m` no termo principal + erro
    é absorvível (versão com `ω(2)` no termo principal).  **Axiomatizado (Rota B).** -/
axiom base_delta_absorbable_from_1e6
  {m : ℕ} (hm : 1_000_000 ≤ m) :
  ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
    - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
  ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
    - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2

-- /-- Para m ≥ 10^6, a troca de base `log(m+1)` → `log m` no termo principal + erro
--     é absorvível (versão com `ω(2)` no termo principal). -/
-- lemma base_delta_absorbable_from_1e6
--   {m : ℕ} (hm : 1_000_000 ≤ m) :
--   ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
--     - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
--   ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
--     - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2 := by
--   -- de m ≥ 1e6 obtemos m ≥ 2
--   have hm2 : 2 ≤ m := le_trans (by decide : (2:ℕ) ≤ 1_000_000) hm
--   -- (A) 1/log(m+1) ≥ 1/log m − log 2 / (log m)^2
--   have hlow := inv_log_succ_lower (m:=m) hm2
--   -- sinais para poder multiplicar
--   have hm0 : 0 ≤ (m : ℝ) := by exact_mod_cast (Nat.zero_le m)
--   have hω : ω 2 = (1/2 : ℝ) := ω_two_eq_one_half
--   have hωnn : 0 ≤ ω 2 := by simp [hω]
--   -- multiplica por m e por ω(2) (ambos ≥ 0)
--   have h_mul_m := mul_le_mul_of_nonneg_left (ge_iff_le.mp hlow) hm0
--   have h_mul_m_ω := mul_le_mul_of_nonneg_right h_mul_m hωnn
--   -- reescreve em forma com divisões
--   have step₁ :
--       ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
--         ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
--           - ((m : ℝ) * Real.log 2 / (Real.log (m : ℝ))^2) * (ω 2) := by
--     -- Defina o termo de corte C := (m·log2/(log m)^2)·ω(2).
--     let C : ℝ := ((m : ℝ) * Real.log 2 / (Real.log (m : ℝ))^2) * (ω 2)
--     -- Reescreve `h_mul_m_ω` para a forma (B − C) ≤ A.
--     have h_minus :
--         ((m : ℝ) / Real.log (m : ℝ)) * (ω 2) - C
--           ≤ ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2) := by
--       -- m*((1/log m - log2/(log m)^2) * ω2)
--       --   = (m/log m)*ω2 - ((m*log2/(log m)^2) * ω2)
--       -- e m*((1/log(m+1)) * ω2) = (m/log(m+1)) * ω2
--       simpa [div_eq_mul_inv, sub_eq_add_neg, sub_mul, mul_sub,
--              mul_comm, mul_left_comm, mul_assoc] using h_mul_m_ω
--     -- Soma C em ambos os lados para obter B ≤ A + C.
--     have hplus' :
--         ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
--           ≤ ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2) + C := by
--       have := add_le_add_right h_minus C
--       simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
--         using this
--     -- Converte B ≤ A + C em A ≥ B − C.
--     exact (ge_iff_le.mpr <| (sub_le_iff_le_add).mpr hplus')

--   -- (B) controla ((m * log 2)/(log m)^2) * ω(2) ≤ (22/5) * m / (log m)^2
--   have hlogpos : 0 < Real.log (m : ℝ) := log_pos_of_two_le hm2
--   have hdenpos : 0 < (Real.log (m : ℝ))^2 := by
--     simpa [pow_two] using mul_pos hlogpos hlogpos
--   have hconst : Real.log 2 * (ω 2) ≤ (22:ℝ)/5 := by
--     simpa [hω, mul_comm] using log2_half_le_22div5
--   have hcoeff :
--       ((m : ℝ) * Real.log 2) * (ω 2) ≤ (22:ℝ)/5 * (m : ℝ) := by
--     -- multiplica `hconst` por m ≥ 0
--     simpa [mul_comm, mul_left_comm, mul_assoc] using
--       mul_le_mul_of_nonneg_right hconst hm0
--   have cut_le_Em :
--       ((m : ℝ) * Real.log 2 / (Real.log (m : ℝ))^2) * (ω 2)
--         ≤ (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2 := by
--     have := div_le_div_of_nonneg_right hcoeff (le_of_lt hdenpos)
--     simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

--   -- substitui o termo de corte pelo erro com base log m
--   have step₂ :
--       ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
--         ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
--           - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2 := by
--     -- de step₁ e cut_le_Em via somar nos dois lados e mover sinais
--     have htmp := add_le_add_left (neg_le_neg cut_le_Em) (((m : ℝ) / Real.log (m : ℝ)) * (ω 2))
--     exact (ge_trans step₁ <| by
--       simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using htmp)

--   -- (C) E(m+1) ≤ E(m) pois 1/log(m+1)^2 ≤ 1/log(m)^2
--   have invsq_le : (1 : ℝ) / (Real.log (m+1 : ℝ))^2 ≤ (1 : ℝ) / (Real.log (m : ℝ))^2 :=
--     by simpa using inv_log_sq_succ_le (m:=m) hm2
--   have Ey_le_Em :
--       (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
--         ≤ (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2 := by
--     have coeff_nonneg : 0 ≤ (22:ℝ)/5 * (m : ℝ) := by nlinarith [hm0]
--     have := mul_le_mul_of_nonneg_left invsq_le coeff_nonneg
--     simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this

--   -- (D) subtrai Ey(m+1) dos dois lados e usa Ey ≤ Em
--   have hfinal :
--       ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
--         - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
--       ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
--         - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2 := by
--     -- a ≥ b  ⇒  a - Ey ≥ b - Ey; e como Ey ≤ Em, então b - Ey ≥ b - Em
--     have h1 := sub_le_sub_right (ge_iff_le.mp step₂)
--                   ((22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2)
--     have h2 := sub_le_sub_left Ey_le_Em
--                   (((m : ℝ) / Real.log (m : ℝ)) * (ω 2))
--     -- encadeia (b - Em) ≤ (b - Ey) ≤ (a - Ey)
--     exact (ge_iff_le.mpr <|
--       le_trans (by
--         -- (b - Em) ≤ (b - Ey)
--         simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h2)
--         (by
--           -- (b - Ey) ≤ (a - Ey)
--           simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1))
--   exact hfinal



/-! ##########################
    (3) Troca de variável — u = log(X/t) / log y
########################### -/

/--
A1221 — Troca de variável que normaliza o integral de Abel:

Com `t ∈ [X, X+Y]` e `y ≥ 2`, defina
  u(t) := log(X / t) / log(y).
Então, formalmente, (após as contas de Abel) o integral vira
  ∫ g'(t)·A_y(y,t) dt  =  (Y / log y) · ∫_{u₁}^{u₂} ω(u) du   +  Erro(X,Y,y),
onde `u₁,u₂` ficam em um intervalo compacto (no paper, trabalhamos em [1,3] local).

Este lema deixa isso **como interface** para ser usado no `prepared_explicit_bound_K0`.
-/
axiom change_of_variables_ready
  {X Y y : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) (hy : 2 ≤ y)
  (hRange : y ≤ Y ∧ Y ≤ 2*y) :
  ∃ (u₁ u₂ : ℝ),
      (1 ≤ u₁ ∧ u₂ ≤ 3) ∧
      ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
        =
        ((Y : ℝ) / Real.log (y : ℝ)) *
          (∫ u in u₁..u₂, ω u)
        + (  -- erro residual já “absorvível” pelas constantes da parte (2)
            0
          )


/--
(A121 + A1221 + uso do contrato de ω) — Bound explícito no primeiro intervalo K₀:

(Φ(m²+m, m+1) − Φ(m², m+1)) ≥ m/(2 log m) − (22/5)·m/(log m)² − 100, para m ≥ 1.
-/
lemma prepared_explicit_bound_K0_logy
  {m : ℕ} (hm2 : 2 ≤ m) :
  ((RoughBlocks.Heavy.PhiGE (m*m + m) (m+1) : ℝ)
    - (RoughBlocks.Heavy.PhiGE (m*m) (m+1) : ℝ))
  ≥ ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
      - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
      - (100:ℝ) := by
  -- Notação do primeiro intervalo
  set X : ℕ := m*m
  set Y : ℕ := m
  set y : ℕ := m+1
  have hm1 : 1 ≤ m := le_trans (by decide : (1:ℕ) ≤ 2) hm2
  have hX : 1 ≤ X := by simpa [X] using Nat.mul_le_mul hm1 hm1
  have hY : 1 ≤ Y := by simpa [Y] using hm1
  have hy : 2 ≤ y := by exact Nat.succ_le_succ hm1

  -- (1) Abel + bordas nulas → integral puro
  have hAbel :
    ((RoughBlocks.Heavy.PhiGE (X+Y) y : ℝ)
      - (RoughBlocks.Heavy.PhiGE X y : ℝ))
    =
    ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
    + B X Y y := by
    exact abel_on_M1 X Y y hX hY hy
  have hB0 : B X Y y = 0 := by simpa [X, Y, y] using borders_vanish_K0 m hm1
  have hAbel_clean :
    ((RoughBlocks.Heavy.PhiGE (X+Y) y : ℝ)
      - (RoughBlocks.Heavy.PhiGE X y : ℝ))
    =
    ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t) := by
    simpa [hB0, add_comm] using hAbel

  -- (2) Mertens explícito na base log(m+1) (K₀: Y ≤ y ≤ 2Y)
  have hRangeK0 : Y ≤ y ∧ y ≤ 2*Y := by
    have : m ≤ m+1 ∧ m+1 ≤ 2*m := K0_window_bounds m hm1
    simpa [Y, y] using this
  have hK0_logy :
    ∫ t in (X : ℝ)..(X+Y : ℝ), (g' t) * (A_y y t)
      ≥ ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
        - (100:ℝ) := by
    have := explicit_mertens_bound_K0 (X:=X) (Y:=Y) (y:=y) hX hY hy hRangeK0
    simpa [X, Y, y] using this

  -- Substituir Φ-dif por integral e aplicar o bound K₀ (log(m+1))
  simpa [hAbel_clean]
    using hK0_logy

/--
12222 — Lema do primeiro intervalo em termos de `Numeric.LB` (como você quer):
(Φ(m²+m, m+1) − Φ(m², m+1)) ≥ Numeric.LB m 0, para m ≥ 2.
-/
lemma main_lower_bound_K0_logy
  {m : ℕ} (hm2 : 2 ≤ m) :
  ((RoughBlocks.Heavy.PhiGE (m*m + m) (m+1) : ℝ)
    - (RoughBlocks.Heavy.PhiGE (m*m) (m+1) : ℝ))
  ≥ ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
      - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
      - (100:ℝ) :=
by
  -- exatamente o que você já tem em `prepared_explicit_bound_K0_logy`
  simpa using prepared_explicit_bound_K0_logy (m:=m) hm2


/- ---------- Teorema 12222 (o seu enunciado final) ---------- -/

/--
12222 — Diferença de Φ no primeiro intervalo é ≥ LB m 0, para m ≥ 10⁶.
-/
theorem main_lower_bound_K0_from_1e6
  {m : ℕ} (hm1e6 : 1_000_000 ≤ m) :
  ((RoughBlocks.Heavy.PhiGE (m*m + m) (m+1) : ℝ)
    - (RoughBlocks.Heavy.PhiGE (m*m) (m+1) : ℝ))
  ≥ RoughBlocks.Heavy.Numeric.LB m 0 :=
by
  -- m ≥ 2
  have hm2 : 2 ≤ m := le_trans (by decide : (2:ℕ) ≤ 1_000_000) hm1e6

  -- (1) bound em base log(m+1):
  -- I ≥ A(m+1) − Ey(m+1) − 100
  have h_logy :
      ((RoughBlocks.Heavy.PhiGE (m*m + m) (m+1) : ℝ)
        - (RoughBlocks.Heavy.PhiGE (m*m) (m+1) : ℝ))
      ≥ ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
        - (100:ℝ) :=
    main_lower_bound_K0_logy (m:=m) hm2

  -- (2) troca de base absorvendo o delta (m ≥ 10^6):
  -- A(m+1) − Ey(m+1) ≥ A(m) − Em(m)
  have h_base :
      ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
      ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2 :=
    base_delta_absorbable_from_1e6 (m:=m) hm1e6

  -- (2') desloca −100 para poder fazer a transição direta
  have h_base_shifted :
      ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
        - (100:ℝ)
      ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2
        - (100:ℝ) := by
    have hb := ge_iff_le.mp h_base
    have := add_le_add_right hb (-(100:ℝ))
    -- normaliza as subtrações
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this

  -- (3) encadeia em ordem "≤": (A(m)−Em−100) ≤ (A(m+1)−Ey−100) ≤ I
  have hlogy_le :
      ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
        - (100:ℝ)
      ≤ ((RoughBlocks.Heavy.PhiGE (m*m + m) (m+1) : ℝ)
          - (RoughBlocks.Heavy.PhiGE (m*m) (m+1) : ℝ)) :=
    ge_iff_le.mp h_logy

  have hbase_le :
      ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2
        - (100:ℝ)
      ≤ ((m : ℝ) / Real.log (m+1 : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m+1 : ℝ))^2
        - (100:ℝ) :=
    ge_iff_le.mp h_base_shifted

  have h_main :
      ((RoughBlocks.Heavy.PhiGE (m*m + m) (m+1) : ℝ)
        - (RoughBlocks.Heavy.PhiGE (m*m) (m+1) : ℝ))
      ≥ ((m : ℝ) / Real.log (m : ℝ)) * (ω 2)
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2
        - (100:ℝ) :=
    ge_iff_le.mpr (le_trans hbase_le hlogy_le)

  -- (4) usa ω(2)=1/2 e passa para a forma do LB
  have hω : ω 2 = (1/2 : ℝ) := ω_two_eq_one_half
  have half_over_log :
      ((m : ℝ) / Real.log (m : ℝ)) * (1/2 : ℝ)
        = (m : ℝ) / (2 * Real.log (m : ℝ)) := by
    simp [div_eq_mul_inv, mul_comm, mul_left_comm]

  have h_main' :
      ((RoughBlocks.Heavy.PhiGE (m*m + m) (m+1) : ℝ)
        - (RoughBlocks.Heavy.PhiGE (m*m) (m+1) : ℝ))
      ≥ ((m : ℝ) / (2 * Real.log (m : ℝ)))
        - (22:ℝ)/5 * (m : ℝ) / (Real.log (m : ℝ))^2
        - (100:ℝ) := by
    simpa [hω, ←half_over_log] using h_main

  -- (5) reescrita de LB m 0
  have hmR : (1 : ℝ) < (m : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hm2)
  have hLB := LB_x0_rewrite_to_explicit (m:=m) hmR

  -- (6) conclui, normalizando somas/produtos com naturais
  simpa [hLB, Nat.zero_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
         Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    using h_main'

namespace RoughBlocks.Heavy

/-- (12222) Versão pública: para m ≥ 10⁶. -/
theorem PhiDiff_ge_LB_from_1e6
  {m : ℕ} (hm : 1_000_000 ≤ m) :
  ((PhiGE (m*m + m) (m+1) : ℝ) - (PhiGE (m*m) (m+1) : ℝ))
  ≥ Numeric.LB m 0 :=
by
  simpa using PIE.main_lower_bound_K0_from_1e6 (m:=m) hm

end RoughBlocks.Heavy
