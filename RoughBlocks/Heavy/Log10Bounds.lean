/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic

namespace RoughBlocks.Heavy
namespace Log10Bounds

open scoped BigOperators Topology

-- Aumenta o limite de heartbeat para evitar timeout em reduções intensivas.
set_option maxHeartbeats 2000000

/-!
# RoughBlocks.Heavy.Log10Bounds

Cotas formais para `log 10`:
- `23/10 ≤ log 10`
- `log 10 ≤ 231/100`

Estratégia:
- Inferior: `exp(23/10) ≤ 10` via majorante geométrico da cauda da série de `exp`.
- Superior: `10 ≤ exp(231/100)` via soma parcial (grau 7) com termos não-negativos.
-/

/-- Passo aritmético: `(k+9)! ≥ 9! ⋅ 10^k`. -/
lemma factorial_step_ge_pow10 (k : ℕ) :
    Nat.factorial (k+9) ≥ Nat.factorial 9 * 10^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk10 : 10 ≤ k+10 := by nlinarith
      have h₁ : Nat.factorial (k+10) = (k+10) * Nat.factorial (k+9) := by rw [Nat.factorial_succ]
      have h₂ : (k+10) * Nat.factorial (k+9) ≥ 10 * (Nat.factorial 9 * 10^k) :=
        Nat.mul_le_mul hk10 ih
      simpa [h₁, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h₂

/-- Majorante geométrico da cauda de `exp x` a partir de `n = 9`, em `x = 23/10`. -/
lemma exp_tail_le_geo_bound_23_tenths :
    let x : ℝ := 23 / 10
    let r : ℝ := 23 / 100
    (0 < r ∧ r < 1) ∧
    (∑' k, x^(k+9)/(Nat.factorial (k+9):ℝ))
      ≤ (x^9/(Nat.factorial 9:ℝ)) * (1/(1-r)) := by
  intro x r
  have hx : x = 23/10 := rfl
  have hr : r = 23/100 := rfl
  have hpos : 0 < r := by norm_num
  have hlt1 : r < 1 := by norm_num
  constructor
  · exact ⟨hpos, hlt1⟩
  -- Comparação termo a termo com progressão geométrica (razão r).
  have hterm : ∀ k, x^(k+9)/(Nat.factorial (k+9):ℝ)
      ≤ (x^9/(Nat.factorial 9:ℝ)) * r^k := by
    intro k
    have hk : (Nat.factorial (k+9):ℝ) ≥ (Nat.factorial 9:ℝ)*((10:ℝ))^k := by
      exact_mod_cast factorial_step_ge_pow10 k
    have hposf : 0 < (Nat.factorial (k+9):ℝ) := by exact_mod_cast Nat.factorial_pos (k+9)
    have hposg : 0 < (Nat.factorial 9 : ℝ) * (10 : ℝ) ^ k := by
      have h1 : 0 < (Nat.factorial 9 : ℝ) := by exact_mod_cast Nat.factorial_pos 9
      have h2 : 0 < (10 : ℝ) ^ k := pow_pos (by norm_num) k
      exact mul_pos h1 h2
    have hk' : (Nat.factorial 9 : ℝ) * (10 : ℝ) ^ k ≤ (Nat.factorial (k+9) : ℝ) := hk
    have hinv : (1 : ℝ) / (Nat.factorial (k+9) : ℝ) ≤ (1 : ℝ) / ((Nat.factorial 9 : ℝ) * (10 : ℝ) ^ k) :=
      (one_div_le_one_div hposf hposg).mpr hk'
    have hx0 : 0 ≤ x := by simp [hx]; norm_num
    have hxpow : 0 ≤ x^(k+9) := pow_nonneg hx0 (k+9)
    have step1 : x^(k+9)/(Nat.factorial (k+9):ℝ) ≤ x^(k+9)/((Nat.factorial 9:ℝ)*(10:ℝ)^k) := by
      calc
        x^(k+9)/(Nat.factorial (k+9):ℝ) = x^(k+9) * (1 / (Nat.factorial (k+9):ℝ)) := by ring
        _ ≤ x^(k+9) * (1 / ((Nat.factorial 9:ℝ)*(10:ℝ)^k)) := by
          exact mul_le_mul_of_nonneg_left hinv hxpow
        _ = x^(k+9)/((Nat.factorial 9:ℝ)*(10:ℝ)^k) := by ring

    have eq1 : x^(k+9)/((Nat.factorial 9:ℝ)*(10:ℝ)^k) = (x^9/(Nat.factorial 9:ℝ)) * (r)^k := by
      calc
        x^(k+9)/((Nat.factorial 9:ℝ)*(10:ℝ)^k) = (x^9 * x^k) / (↑(Nat.factorial 9) * (10:ℝ)^k) := by ring
        _ = (x^9 / ↑(Nat.factorial 9)) * (x^k / (10:ℝ)^k) := by ring
        _ = (x^9 / ↑(Nat.factorial 9)) * ((x/10)^k) := by rw [←div_pow]
        _ = (x^9 / ↑(Nat.factorial 9)) * (r^k) := by rw [show x/10 = r by rw [hx, hr]; ring]

    rw [eq1] at step1
    exact step1
  -- Soma geométrica fechada e comparação de séries.
  have hgeo_sum : HasSum (λ k : ℕ => r ^ k) (1 - r)⁻¹ :=
    have := hasSum_geometric_of_lt_one (le_of_lt hpos) hlt1
    this
  have geo : (∑' k : ℕ, r ^ k) = (1 - r)⁻¹ := hgeo_sum.tsum_eq
  have summable_rhs : Summable (λ k => (x^9 / (Nat.factorial 9 : ℝ)) * r ^ k) := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (le_of_lt hpos) hlt1
  have hsum : (∑' k, x^(k+9)/(Nat.factorial (k+9):ℝ)) ≤ (∑' k, (x^9/(Nat.factorial 9:ℝ)) * r^k) := by
    have summable_lhs : Summable (fun k => x ^ (k + 9) / ↑(Nat.factorial (k + 9))) :=
      (Real.summable_pow_div_factorial x).comp_injective (add_left_injective 9)
    exact Summable.tsum_le_tsum hterm summable_lhs summable_rhs
  calc
    (∑' k, x^(k+9)/(Nat.factorial (k+9):ℝ)) ≤ (∑' k, (x^9/(Nat.factorial 9:ℝ)) * r^k) := hsum
    _ = (x^9 / (Nat.factorial 9:ℝ)) * (∑' k, r ^ k) := by
      rw [tsum_mul_left]
    _ = (x^9 / (Nat.factorial 9:ℝ)) * ((1 - r)⁻¹) := by rw [geo]
    _ = (x^9 / (Nat.factorial 9:ℝ)) * (1 / (1 - r)) := by ring

/-- **Cota superior** `exp (23/10) ≤ 10`. -/
lemma exp_23_tenths_le_10 : Real.exp (23/10) ≤ 10 := by
  -- `exp` como `tsum`, dividir em soma finita + cauda.
  let f : ℕ → ℝ := fun n => (23/10)^n / (Nat.factorial n : ℝ)
  have hs : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial (23/10)
  have hexp : Real.exp (23/10) = ∑' n, f n := by
    have h := congrArg (fun (h : ℝ → ℝ) => h (23/10))
      (NormedSpace.exp_eq_tsum_div (𝕂 := ℝ) (𝔸 := ℝ))
    simpa [Real.exp_eq_exp_ℝ, f] using h
  have hsplit' :
      ∑' n, f n = (∑ n ∈ Finset.range 9, f n) + ∑' n, f (n + 9) :=
    (Summable.sum_add_tsum_nat_add 9 hs).symm
  -- Cauda ≤ majorante geométrico específico (lema anterior).
  have ⟨_, htail⟩ := exp_tail_le_geo_bound_23_tenths
  -- Cálculo numérico da parte “soma finita + majorante da cauda”.
  have hnum :
      (∑ n ∈ Finset.range 9, f n)
      + ((23/10)^9 / (Nat.factorial 9 : ℝ)) * (1 / (1 - (23:ℝ)/100))
        ≤ 10 := by
    simp [f] ; norm_num
  -- Junta: `exp = soma + cauda ≤ soma + majorante`.
  have exp_le_sum_plus_geom :
    Real.exp (23/10)
      ≤ (∑ n ∈ Finset.range 9, f n)
        + ((23/10)^9 / (Nat.factorial 9 : ℝ)) * (1 / (1 - (23:ℝ)/100)) := by
    have hineq := add_le_add_left htail (∑ n ∈ Finset.range 9, f n)
    simpa [hexp, hsplit', f, add_comm, add_left_comm, add_assoc] using hineq

  exact exp_le_sum_plus_geom.trans hnum

/-- **Cota inferior** `10 ≤ exp (231/100)`. -/
lemma ten_le_exp_231_hundredths : (10 : ℝ) ≤ Real.exp (231/100) := by
  set x : ℝ := 231/100 with hx
  have hx0 : 0 ≤ x := by norm_num
  -- Soma parcial até grau 7 já é ≥ 10.
  have h_sum_ge_10 :
      10 ≤ ∑ k ∈ Finset.range 8, x^k / (Nat.factorial k : ℝ) := by
    simp [hx]
    norm_num
  -- A soma parcial é ≤ `exp x` (termos não-negativos).
  let f : ℕ → ℝ := fun k => x^k / (Nat.factorial k : ℝ)
  have h_nonneg : ∀ k, 0 ≤ f k := by
    intro k
    dsimp [f]
    exact div_nonneg (pow_nonneg hx0 k) (by exact_mod_cast (Nat.factorial_pos k).le)
  have hs : Summable f := by
    simpa [f] using Real.summable_pow_div_factorial x
  have h_exp_tsum : Real.exp x = ∑' k, f k := by
    have h := congrArg (fun (h : ℝ → ℝ) => h x)
      (NormedSpace.exp_eq_tsum_div (𝕂 := ℝ) (𝔸 := ℝ))
    simpa [Real.exp_eq_exp_ℝ, f] using h
  have h_sum_le_exp :
      ∑ k ∈ Finset.range 8, f k ≤ Real.exp x := by
    have := Summable.sum_le_tsum (s := Finset.range 8)
      (hs := fun _ _ => h_nonneg _)
      (hf := hs)
    simpa [h_exp_tsum] using this
  exact h_sum_ge_10.trans h_sum_le_exp

/-- **Cotas para `log (10^6)`**: `(69/5) ≤ log(10^6) ≤ (693/50)`. -/
lemma log_1e6_bounds :
  (69 : ℝ) / 5 ≤ Real.log (1_000_000 : ℝ) ∧ Real.log (1_000_000 : ℝ) ≤ (693 : ℝ) / 50 := by
  have hpos10 : 0 < (10 : ℝ) := by norm_num
  have hpos1e6 : 0 < (1_000_000 : ℝ) := by norm_num
  constructor
  · -- Esquerda: `exp(69/5) ≤ 10^6`.
    have hlog10 : (23 : ℝ) / 10 ≤ Real.log (10 : ℝ) :=
      (Real.le_log_iff_exp_le hpos10).mpr exp_23_tenths_le_10
    have hexp : Real.exp ((69 : ℝ) / 5) ≤ Real.exp (6 * Real.log (10 : ℝ)) := by
      have hmul : 6 * ((23 : ℝ) / 10) ≤ 6 * Real.log (10 : ℝ) :=
        mul_le_mul_of_nonneg_left hlog10 (by norm_num)
      have : (69 : ℝ) / 5 = 6 * ((23 : ℝ) / 10) := by norm_num
      simpa [this] using (Real.exp_le_exp.mpr hmul)
    have hpow : Real.exp (6 * Real.log (10 : ℝ)) = (10 : ℝ) ^ 6 := by
      simpa [Real.exp_log hpos10] using Real.exp_nat_mul (n := 6) (x := Real.log (10 : ℝ))
    have : Real.exp ((69 : ℝ) / 5) ≤ (1_000_000 : ℝ) := by
      calc
        Real.exp ((69 : ℝ) / 5) ≤ (10 : ℝ) ^ 6 := by simpa [hpow] using hexp
        _ = (1_000_000 : ℝ) := by norm_num
    exact (Real.le_log_iff_exp_le hpos1e6).mpr this
  · -- Direita: `10^6 ≤ exp(693/50)`.
    have hlog10_hi : Real.log (10 : ℝ) ≤ (231 : ℝ) / 100 :=
      (Real.log_le_iff_le_exp hpos10).mpr ten_le_exp_231_hundredths
    have hexp : Real.exp (6 * Real.log (10 : ℝ)) ≤ Real.exp ((693 : ℝ) / 50) := by
      have hmul : 6 * Real.log (10 : ℝ) ≤ 6 * ((231 : ℝ) / 100) :=
        mul_le_mul_of_nonneg_left hlog10_hi (by norm_num)
      have : (693 : ℝ) / 50 = 6 * ((231 : ℝ) / 100) := by norm_num
      simpa [this] using (Real.exp_le_exp.mpr hmul)
    have hpow : Real.exp (6 * Real.log (10 : ℝ)) = (10 : ℝ) ^ 6 := by
      simpa [Real.exp_log hpos10] using Real.exp_nat_mul (n := 6) (x := Real.log (10 : ℝ))
    have : (1_000_000 : ℝ) ≤ Real.exp ((693 : ℝ) / 50) := by
      have h10pow : (10 : ℝ) ^ 6 ≤ Real.exp ((693 : ℝ) / 50) := by simpa [hpow] using hexp
      have eq10pow : (1_000_000 : ℝ) = (10 : ℝ) ^ 6 := by norm_num
      simpa [eq10pow] using h10pow
    exact (Real.log_le_iff_le_exp hpos1e6).mpr this

/-- Passo aritmético: `(k+6)! ≥ 6! ⋅ 7^k`. -/
lemma factorial_step_ge_pow7 (k : ℕ) :
    Nat.factorial (k+6) ≥ Nat.factorial 6 * 7^k := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hk7 : 7 ≤ k+7 := by simp
      have h₁ : Nat.factorial (k+7) = (k+7) * Nat.factorial (k+6) := by
        simpa using Nat.factorial_succ (k+6)
      have h₂ : (k+7) * Nat.factorial (k+6) ≥ 7 * (Nat.factorial 6 * 7^k) := by
        exact Nat.mul_le_mul hk7 ih
      simpa [h₁, pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h₂

/-- Cauda geométrica de `exp x` para `x = 3/5`, a partir de `k = 6`.
Mostra que `∑' k, x^(k+6)/(k+6)! ≤ (x^6/6!) * (1/(1-q))` com `q = x/7 = 3/35`. -/
lemma exp_three_fifths_tail_bound :
  (∑' k : ℕ, ((3:ℝ)/5)^(k+6) / (Nat.factorial (k+6) : ℝ))
    ≤ ((3:ℝ)/5)^6 / (Nat.factorial 6 : ℝ) * (1 / (1 - ((3:ℝ)/35))) := by
  set x : ℝ := (3:ℝ)/5
  set q : ℝ := x / 7
  have hx : x = (3:ℝ)/5 := rfl
  have hq : q = x / 7 := rfl
  have hq_pos : 0 < q := by
    have hxpos : 0 < x := by
      norm_num [hx]
    rw [hq]
    exact div_pos hxpos (by norm_num)
  have hq' : q = (3:ℝ)/35 := by
    have : (3:ℝ)/5 / 7 = (3:ℝ)/35 := by norm_num
    simpa [hq, hx] using this
  have hq_lt1 : q < 1 := by
    simpa [hq'] using (by norm_num : (3:ℝ)/35 < 1)
  -- Dominação termo a termo por progressão geométrica (razão q = x/7).
  have hterm : ∀ k, x^(k+6)/(Nat.factorial (k+6):ℝ)
      ≤ (x^6/(Nat.factorial 6:ℝ)) * q^k := by
    intro k
    have hk : (Nat.factorial (k+6):ℝ) ≥ (Nat.factorial 6:ℝ) * (7:ℝ)^k := by
      exact_mod_cast factorial_step_ge_pow7 k
    have hposf : 0 < (Nat.factorial (k+6):ℝ) := by exact_mod_cast Nat.factorial_pos (k+6)
    have hposg : 0 < (Nat.factorial 6 : ℝ) * (7 : ℝ) ^ k := by
      have h1 : 0 < (Nat.factorial 6 : ℝ) := by exact_mod_cast Nat.factorial_pos 6
      have h2 : 0 < (7 : ℝ) ^ k := pow_pos (by norm_num) k
      exact mul_pos h1 h2
    have hk' : (Nat.factorial 6 : ℝ) * (7 : ℝ) ^ k ≤ (Nat.factorial (k+6) : ℝ) := hk
    have hinv : (1 : ℝ) / (Nat.factorial (k+6) : ℝ) ≤ (1 : ℝ) / ((Nat.factorial 6 : ℝ) * (7 : ℝ) ^ k) :=
      (one_div_le_one_div hposf hposg).mpr hk'
    have hx0 : 0 ≤ x := by simp [hx]; norm_num
    have hxpow : 0 ≤ x^(k+6) := pow_nonneg hx0 (k+6)
    have step1 : x^(k+6)/(Nat.factorial (k+6):ℝ)
                ≤ x^(k+6)/((Nat.factorial 6:ℝ)*(7:ℝ)^k) := by
      calc
        x^(k+6)/(Nat.factorial (k+6):ℝ) = x^(k+6) * (1 / (Nat.factorial (k+6):ℝ)) := by ring
        _ ≤ x^(k+6) * (1 / ((Nat.factorial 6:ℝ)*(7:ℝ)^k)) := by
          exact mul_le_mul_of_nonneg_left hinv hxpow
        _ = x^(k+6)/((Nat.factorial 6:ℝ)*(7:ℝ)^k) := by ring
    have eq1' : x^(k+6)/((Nat.factorial 6:ℝ)*(7:ℝ)^k)
              = (x^6/(Nat.factorial 6:ℝ)) * (q)^k := by
      calc
        x^(k+6)/((Nat.factorial 6:ℝ)*(7:ℝ)^k)
            = (x^6 * x^k) / (↑(Nat.factorial 6) * (7:ℝ)^k) := by ring
        _ = (x^6 / ↑(Nat.factorial 6)) * (x^k / (7:ℝ)^k) := by ring
        _ = (x^6 / ↑(Nat.factorial 6)) * ((x/7)^k) := by rw [←div_pow]
        _ = (x^6 / ↑(Nat.factorial 6)) * (q^k) := by simp [hq]
    have : x^(k+6)/(Nat.factorial (k+6):ℝ)
            ≤ (x^6/(Nat.factorial 6:ℝ)) * (q)^k := by
      have := step1
      simpa [eq1'] using this
    exact this
  -- Soma geométrica e reorganização do `tsum`.
  have summable_lhs : Summable (fun k => x ^ (k + 6) / ↑(Nat.factorial (k + 6))) :=
    (Real.summable_pow_div_factorial x).comp_injective (add_left_injective 6)
  have summable_rhs : Summable (fun k => (x^6 / (Nat.factorial 6 : ℝ)) * q ^ k) := by
    apply Summable.mul_left
    exact summable_geometric_of_lt_one (le_of_lt hq_pos) hq_lt1
  have hsum : (∑' k, x^(k+6)/(Nat.factorial (k+6):ℝ))
            ≤ (∑' k, (x^6/(Nat.factorial 6:ℝ)) * q^k) := by
    exact Summable.tsum_le_tsum hterm summable_lhs summable_rhs
  have geo : (∑' k : ℕ, q ^ k) = (1 - q)⁻¹ :=
    (hasSum_geometric_of_lt_one (le_of_lt hq_pos) hq_lt1).tsum_eq
  have hfinal :
      (∑' k, x^(k+6)/(Nat.factorial (k+6):ℝ))
        ≤ (x^6 / (Nat.factorial 6:ℝ)) * (1 / (1 - q)) := by
    calc
      (∑' k, x^(k+6)/(Nat.factorial (k+6):ℝ)) ≤ (∑' k, (x^6/(Nat.factorial 6:ℝ)) * q^k) := hsum
      _ = (x^6 / (Nat.factorial 6:ℝ)) * (∑' k, q^k) := by rw [tsum_mul_left]
      _ = (x^6 / (Nat.factorial 6:ℝ)) * (1 - q)⁻¹ := by simp [geo]
      _ = (x^6 / (Nat.factorial 6:ℝ)) * (1 / (1 - q)) := by ring
  simpa [hq']
    using hfinal

/-- **Cota superior** `exp (3/5) ≤ 9397/5000`. -/
lemma exp_three_fifths_le_9397_div_5000 :
  Real.exp ((3 : ℝ)/5) ≤ (9397 : ℝ) / 5000 := by
  set x : ℝ := (3:ℝ)/5
  -- `exp x =` soma finita (até k=5) + cauda (a partir de k=6).
  let f : ℕ → ℝ := fun n => x^n / (Nat.factorial n : ℝ)
  have hs : Summable f := by
    simpa [f, x] using Real.summable_pow_div_factorial x
  have h_exp_tsum : Real.exp x = ∑' n, f n := by
    have h := congrArg (fun (h : ℝ → ℝ) => h x)
      (NormedSpace.exp_eq_tsum_div (𝕂 := ℝ) (𝔸 := ℝ))
    simpa [Real.exp_eq_exp_ℝ, f] using h
  have split :
      Real.exp x
        = (Finset.sum (Finset.range 6) (fun k => x^k / (Nat.factorial k : ℝ)))
          + (∑' k : ℕ, x^(k+6) / (Nat.factorial (k+6) : ℝ)) := by
    simpa [f, h_exp_tsum] using
      (Summable.sum_add_tsum_nat_add 6 hs).symm
  -- Aplica a cota da cauda (lema anterior) e fecha numericamente.
  have tail_le := exp_three_fifths_tail_bound
  have sum_plus_tail_le_9397 :
    (Finset.sum (Finset.range 6) (fun k => x^k / (Nat.factorial k : ℝ)))
    + (∑' k : ℕ, x^(k+6) / (Nat.factorial (k+6) : ℝ))
    ≤ (9397 : ℝ) / 5000 := by
    have tail_le_geom :
      (∑' k : ℕ, x^(k+6) / (Nat.factorial (k+6) : ℝ))
      ≤ x^6 / (Nat.factorial 6 : ℝ) * (1 / (1 - (3:ℝ)/35)) := by
      simpa [x] using tail_le
    have sum_add_tail_le :=
      add_le_add_left tail_le_geom (Finset.sum (Finset.range 6) (fun k => x^k / (Nat.factorial k : ℝ)))
    have numeric_bound :
      (Finset.sum (Finset.range 6) (fun k => x^k / (Nat.factorial k : ℝ)))
        + (x^6 / (Nat.factorial 6 : ℝ) * (1 / (1 - (3:ℝ)/35)))
        ≤ (9397 : ℝ) / 5000 := by
      norm_num [x]
    exact le_trans (by simpa using sum_add_tail_le) numeric_bound
  simpa [split] using sum_plus_tail_le_9397

/-- **Cotas para `log 18794`**: `(98/10) ≤ log(18794) ≤ (987/100)`. -/
lemma log_18794_bounds :
  (98 : ℝ) / 10 ≤ Real.log (18794 : ℝ) ∧ Real.log (18794 : ℝ) ≤ (987 : ℝ) / 100 := by
  have hpos10 : 0 < (10 : ℝ) := by norm_num
  have hpos : 0 < (18794 : ℝ) := by norm_num
  constructor
  · -- Esquerda: `exp(9.8) ≤ 18794`.
    have hlog10_lo : (23 : ℝ) / 10 ≤ Real.log (10 : ℝ) :=
      (Real.le_log_iff_exp_le hpos10).mpr (by
        have := by
          exact Log10Bounds.exp_23_tenths_le_10
        simpa using this)
    have hmul : 4 * ((23 : ℝ) / 10) ≤ 4 * Real.log (10 : ℝ) :=
      mul_le_mul_of_nonneg_left hlog10_lo (by norm_num)
    have hx : Real.exp (4 * Real.log (10:ℝ)) = (10:ℝ)^4 := by
      simpa [Real.exp_log hpos10] using Real.exp_nat_mul (n := 4) (x := Real.log (10:ℝ))
    have : Real.exp ((98 : ℝ)/10)
            ≤ (10 : ℝ)^4 * Real.exp ((3:ℝ)/5) := by
      have hsplit : (98:ℝ)/10 = 4 * ((23 : ℝ) / 10) + (3 : ℝ) / 5 := by norm_num
      have hineq : 4*((23:ℝ)/10) + (3:ℝ)/5 ≤ 4*Real.log (10:ℝ) + (3:ℝ)/5 :=
        add_le_add_right hmul _
      have hexp_le : Real.exp ((98 : ℝ)/10) ≤ Real.exp (4*Real.log (10:ℝ) + (3:ℝ)/5) := by
        simpa [hsplit] using (Real.exp_le_exp.mpr hineq)
      simpa [Real.exp_add, hx] using hexp_le
    have hnum : (10:ℝ)^4 * Real.exp ((3:ℝ)/5) ≤ (18794 : ℝ) := by
      have exp_three_fifths_bound := exp_three_fifths_le_9397_div_5000
      have mul_bound :
        (10:ℝ)^4 * Real.exp ((3:ℝ)/5) ≤ (10:ℝ)^4 * ((9397:ℝ)/5000) :=
        mul_le_mul_of_nonneg_left exp_three_fifths_bound (by norm_num)
      simpa using (mul_bound.trans_eq (by norm_num : (10:ℝ)^4 * ((9397:ℝ)/5000) = (18794:ℝ)))
    exact (Real.le_log_iff_exp_le hpos).mpr ((le_trans this hnum))
  · -- Direita: `18794 ≤ exp(9.87)` por soma parcial positiva.
    set y : ℝ := (987 : ℝ) / 100
    have hx0 : 0 ≤ y := by norm_num [y]
    let f : ℕ → ℝ := fun k => y^k / (Nat.factorial k : ℝ)
    have h_nonneg : ∀ k, 0 ≤ f k := by
      intro k; dsimp [f]
      have hkpos : 0 < (Nat.factorial k : ℝ) := by exact_mod_cast (Nat.factorial_pos k)
      exact div_nonneg (pow_nonneg hx0 k) hkpos.le
    have hs : Summable f := by simpa [f, y] using Real.summable_pow_div_factorial y
    have h_exp_tsum : Real.exp y = ∑' k, f k := by
      have h := congrArg (fun (h : ℝ → ℝ) => h y)
        (NormedSpace.exp_eq_tsum_div (𝕂 := ℝ) (𝔸 := ℝ))
      simpa [Real.exp_eq_exp_ℝ, f] using h
    -- 17 termos excedem `18794` (checagem aritmética).
    have hsum_ge : (18794 : ℝ) ≤ ∑ k ∈ Finset.range 17, f k := by
      norm_num [f, y]
    -- Soma finita ≤ `exp y`.
    have hsum_le_exp : ∑ k ∈ Finset.range 17, f k ≤ Real.exp y := by
      have sum_le_tsum_nonneg :=
        Summable.sum_le_tsum (s := Finset.range 17) (hf := hs) (hs := fun k _ => h_nonneg k)
      simpa [h_exp_tsum] using sum_le_tsum_nonneg
    have : (18794 : ℝ) ≤ Real.exp y := le_trans hsum_ge hsum_le_exp
    exact (Real.log_le_iff_le_exp hpos).mpr (by simpa [y] using this)

end Log10Bounds
end RoughBlocks.Heavy
