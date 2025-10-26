/-
SPDX-License-Identifier: Apache-2.0

Parte 2 (enxuta): apenas o que a Parte 4 usa.
- Mostra que u ∈ [2,3] para m ≥ U0Default e x ≤ 8;
- Ponte elementar: LB ≥ margin (via ω(u) ≥ 1/3 em [2,3]).

Sem dependência de `RoughBlocks.Heavy.Numeric`: definimos `LB` e `margin`
aqui mesmo, em `RoughBlocks.Heavy`.
-/

import Mathlib
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.Omega

/- As definições canônicas `LB` e `margin` ficam no namespace `RoughBlocks.Heavy`,
   para que a Parte 4 as use apenas com `open RoughBlocks.Heavy`. -/
namespace RoughBlocks.Heavy
noncomputable section
open Real

/-- Lado analítico no bloco (y = m, X = m^2 + x m, Y = m). -/
noncomputable def LB (m x : ℕ) : ℝ :=
  ((m : ℝ) / Real.log (m : ℝ)) *
    omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ))
  - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
  - (C2Default : ℝ)

/-- `margin m`: cota trocando `ω(u) ≥ 1/3` em `u ∈ [2,3]`. -/
noncomputable def margin (m : ℕ) : ℝ :=
  ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ) / 3)
  - C1Default * ((m : ℝ) / (Real.log (m : ℝ))^2)
  - (C2Default : ℝ)

end
end RoughBlocks.Heavy

namespace RoughBlocks.External.Certs
noncomputable section

open Classical Real
open RoughBlocks.Heavy

/-- `log m > 0` para `m ≥ 2`. -/
lemma log_pos_of_ge_two {m : ℕ} (hm : 2 ≤ m) : 0 < Real.log (m : ℝ) := by
  have hm1 : (1 : ℝ) < (m : ℝ) :=
    by exact_mod_cast (lt_of_lt_of_le (by decide : (1:ℕ) < 2) hm)
  exact (Real.log_pos_iff (by exact_mod_cast (Nat.zero_le m))).2 hm1

/-- Faixa do bloco: para `m ≥ U0Default` e `x ≤ 8`,
`u = log(m^2 + x m) / log m ∈ [2,3]`. -/
lemma u_block_range_of_ge_U0
  {m x : ℕ} (hm : U0Default ≤ m) (hx : x ≤ 8) :
  (2 : ℝ) ≤ Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ)
∧ Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ) ≤ (3 : ℝ) := by
  -- Preparos: `m ≥ 2` e `m ≥ 8`
  have hm2 : 2 ≤ m := le_trans (by decide : (2:ℕ) ≤ U0Default) hm
  have hm8 : 8 ≤ m := le_trans (by decide : (8:ℕ) ≤ U0Default) hm
  have hlogpos : 0 < Real.log (m : ℝ) := log_pos_of_ge_two hm2
  have hlog_ne  : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlogpos

  -- Notação do bloco
  set X : ℕ := m^2 + x*m
  have hX_ge_m2 : (m^2 : ℕ) ≤ X := by
    dsimp [X]; exact Nat.le_add_right _ _

  -- (i) limite inferior: `log X ≥ 2 log m`
  have hm_pos_nat  : 0 < m := lt_of_lt_of_le (by decide : (0:ℕ) < 2) hm2
  have hm_pos_real : 0 < (m : ℝ) := by exact_mod_cast hm_pos_nat
  have hm2_pos_real : 0 < ((m^2 : ℕ) : ℝ) := by
    have : 0 < m^2 := by
      simpa [pow_two] using Nat.mul_pos hm_pos_nat hm_pos_nat
    exact_mod_cast this
  have hlog_m2 : Real.log ((m^2 : ℕ) : ℝ) = (2 : ℝ) * Real.log (m : ℝ) := by
    simpa [Nat.cast_pow] using Real.log_pow hm_pos_real (2 : ℕ)
  have hlog_le : Real.log ((m^2 : ℕ) : ℝ) ≤ Real.log (X : ℝ) := by
    have : ((m^2 : ℕ) : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX_ge_m2
    exact Real.log_le_log hm2_pos_real this
  have h_left : (2 : ℝ) ≤ Real.log (X : ℝ) / Real.log (m : ℝ) := by
    have := div_le_div_of_nonneg_right hlog_le hlogpos.le
    simpa [hlog_m2, mul_div_assoc, hlog_ne] using this

  -- (ii) limite superior: `X ≤ m^3` (pois `x ≤ 8 ≤ m`)
  have hx_mul_le : x*m ≤ 8*m := Nat.mul_le_mul_right _ hx
  have h8m_le_m2 : 8*m ≤ m^2 := by
    -- m≥8 ⇒ 8*m ≤ m*m
    simpa [pow_two, Nat.mul_comm] using Nat.mul_le_mul_right m hm8

  -- passo chave: 2*m^2 ≤ m^3 (evita o caso ...*2)
  have two_mul_m2_le_m3 : 2 * m^2 ≤ m^3 := by
    have := Nat.mul_le_mul_right (m^2) hm2
    simpa [pow_succ, pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using this

  -- converte para soma e encadeia
  have two_m2_as_sum : m^2 + m^2 ≤ m^3 := by
    simpa [two_mul] using two_mul_m2_le_m3
  have h1 : m^2 + x*m ≤ m^2 + 8*m := Nat.add_le_add_left hx_mul_le _
  have h2 : m^2 + 8*m ≤ m^2 + m^2 := Nat.add_le_add_left h8m_le_m2 _
  have hX_le_m3 : X ≤ m^3 :=
    (le_trans (le_trans h1 h2) two_m2_as_sum)

  -- conclui o lado direito
  have h_right : Real.log (X : ℝ) / Real.log (m : ℝ) ≤ (3 : ℝ) := by
    have hXm3 : (X : ℝ) ≤ ((m^3 : ℕ) : ℝ) := by exact_mod_cast hX_le_m3
    have hposX : 0 < (X : ℝ) := by
      have hm2_pos : 0 < m^2 := by
        simpa [pow_two] using Nat.mul_pos hm_pos_nat hm_pos_nat
      exact_mod_cast lt_of_lt_of_le hm2_pos hX_ge_m2
    have hlog : Real.log (X : ℝ) ≤ Real.log ((m^3 : ℕ) : ℝ) :=
      Real.log_le_log hposX hXm3
    have hpow3 : Real.log ((m^3 : ℕ) : ℝ) = (3 : ℝ) * Real.log (m : ℝ) := by
      simpa [Nat.cast_pow] using Real.log_pow hm_pos_real (3 : ℕ)
    have := div_le_div_of_nonneg_right hlog hlogpos.le
    simpa [hpow3, mul_div_assoc, hlog_ne] using this

  exact ⟨h_left, h_right⟩

/-- Ponte elementar: em `u∈[2,3]` temos `ω(u) ≥ 1/3` ⇒ `LB ≥ margin`, uniformemente
para todo `m ≥ U0Default` e `x ≤ 8`. -/
lemma LB_ge_margin' {m x : ℕ} (hm : U0Default ≤ m) (hx : x ≤ 8) :
  LB m x ≥ margin m := by
  unfold RoughBlocks.Heavy.LB RoughBlocks.Heavy.margin
  have hlogpos : 0 < Real.log (m : ℝ) :=
    log_pos_of_ge_two (le_trans (by decide : (2:ℕ) ≤ U0Default) hm)
  have hcoef_nonneg : 0 ≤ (m : ℝ) / Real.log (m : ℝ) :=
    div_nonneg (by positivity) hlogpos.le
  have hRange := u_block_range_of_ge_U0 (m := m) (x := x) hm hx
  have hω : (1 : ℝ) / 3 ≤
      omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ)) :=
    omega_lower_bound_block hRange.left hRange.right
  have hmain :
      ((m : ℝ) / Real.log (m : ℝ)) *
        omega (Real.log ((m^2 + x*m : ℕ) : ℝ) / Real.log (m : ℝ))
      ≥ ((m : ℝ) / Real.log (m : ℝ)) * ((1 : ℝ) / 3) :=
    mul_le_mul_of_nonneg_left hω hcoef_nonneg
  exact sub_le_sub (sub_le_sub hmain le_rfl) le_rfl

end
end RoughBlocks.External.Certs
