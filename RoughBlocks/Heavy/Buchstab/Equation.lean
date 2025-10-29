/-
SPDX-License-Identifier: Apache-2.0
Part of the RoughBlocks project.
-/

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import RoughBlocks.Heavy.Buchstab.CoreB

set_option maxHeartbeats 5000000

open Real
open MeasureTheory
open Set
open intervalIntegral
open RoughBlocks.Heavy.Buchstab

noncomputable section

/-! ### Auxiliar: ∫ (1/t) = log -/


/-- Para `0 < a ≤ b`,  `∫_a^b (1/t) dt = log b - log a`. -/
lemma integral_one_div_eq_log_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∫ t in a..b, (1 / t) = Real.log b - Real.log a := by
  -- fixe a identidade uIcc = Icc só uma vez (evita `simp` pesado)
  have h_uIcc : uIcc a b = Icc a b := uIcc_of_le hab

  -- HasDerivAt log = 1/x em Icc
  have hHas_Icc :
      ∀ x ∈ Icc a b, HasDerivAt (fun y => Real.log y) (1 / x) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    simpa using Real.hasDerivAt_log hx0

  -- Reescreve para uIcc
  have hHas_uIcc :
      ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.log y) (1 / x) x := by
    intro x hx
    have hx' : x ∈ Icc a b := by simpa [h_uIcc] using hx
    exact hHas_Icc x hx'

  -- 1/x contínua em uIcc (logo integrável no intervalo)
  have hcont_inv_Icc : ContinuousOn (fun y : ℝ => 1 / y) (Icc a b) := by
    have hconst : ContinuousOn (fun _ => (1 : ℝ)) (Icc a b) := continuousOn_const
    have hid    : ContinuousOn (fun y => y) (Icc a b) := continuousOn_id
    have h_nz : ∀ x ∈ Icc a b, x ≠ 0 := by
      intro x hx; exact ne_of_gt (lt_of_lt_of_le ha hx.1)
    exact hconst.div hid h_nz
  have hcont_inv_uIcc :
      ContinuousOn (fun y : ℝ => 1 / y) (uIcc a b) := by
    simpa [h_uIcc] using hcont_inv_Icc
  have h_int_one_div : IntervalIntegrable (fun x => 1 / x) MeasureTheory.volume a b :=
    hcont_inv_uIcc.intervalIntegrable

  -- log contínua em uIcc (requerido por esta versão do TFC)
  have hcont_log_Icc : ContinuousOn (fun y : ℝ => Real.log y) (Icc a b) := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
    simpa using (Real.continuousAt_log hx0).continuousWithinAt
  have hcont_log_uIcc :
      ContinuousOn (fun y : ℝ => Real.log y) (uIcc a b) := by
    simpa [h_uIcc] using hcont_log_Icc

  -- **Use a variante certa**: aceita `HasDerivAt`
  exact
    (intervalIntegral.integral_eq_sub_of_hasDerivAt
      (a := a) (b := b)
      (f := fun y => Real.log y) (f' := fun x => 1 / x)
      hHas_uIcc h_int_one_div)


-- /-- Para `0 < a ≤ b`,  `∫_a^b (1/t) dt = log b - log a`. -/
-- lemma integral_one_div_eq_log_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
--     ∫ t in a..b, (1 / t) = Real.log b - Real.log a := by
--   -- Fixamos esta igualdade para evitar `simp` pesado toda hora.
--   have h_uIcc : uIcc a b = Icc a b := uIcc_of_le hab

--   -- Derivada de log = 1/x em Icc a b (e então em uIcc a b por reescrita).
--   have hderiv_Icc :
--       ∀ x ∈ Icc a b, HasDerivAt (fun y => Real.log y) (1 / x) x := by
--     intro x hx
--     have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
--     simpa using Real.hasDerivAt_log hx0

--   have hderiv_uIcc :
--       ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.log y) (1 / x) x := by
--     intro x hx
--     have hx' : x ∈ Icc a b := by
--       -- reescrevemos uIcc → Icc sem `simp`
--       simpa [h_uIcc] using hx
--     exact hderiv_Icc x hx'

--   -- Continuidade de log em uIcc a b (via Icc a b).
--   have hcont_log_Icc : ContinuousOn (fun y : ℝ => Real.log y) (Icc a b) := by
--     intro x hx
--     have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
--     simpa using (Real.continuousAt_log hx0).continuousWithinAt

--   have hcont_log_uIcc :
--       ContinuousOn (fun y : ℝ => Real.log y) (uIcc a b) := by
--     -- reescrita simples, sem `simp`
--     simpa [h_uIcc] using hcont_log_Icc

--   -- 1/x contínua em uIcc a b (via Icc a b) ⇒ integrável no intervalo
--   have hcont_inv_Icc : ContinuousOn (fun y : ℝ => 1 / y) (Icc a b) := by
--     have hconst : ContinuousOn (fun _ => (1 : ℝ)) (Icc a b) := continuousOn_const
--     have hid    : ContinuousOn (fun y => y) (Icc a b) := continuousOn_id
--     have h_nz : ∀ x ∈ Icc a b, x ≠ 0 := by
--       intro x hx; exact ne_of_gt (lt_of_lt_of_le ha hx.1)
--     exact hconst.div hid h_nz

--   have hcont_inv_uIcc :
--       ContinuousOn (fun y : ℝ => 1 / y) (uIcc a b) := by
--     simpa [h_uIcc] using hcont_inv_Icc

--   have h_int_one_div : IntervalIntegrable (fun x => 1 / x) volume a b :=
--     hcont_inv_uIcc.intervalIntegrable

--   -- Teorema Fundamental do Cálculo (versão com HasDerivAt).
--   exact
--     (intervalIntegral.integral_deriv_eq_sub
--       (a := a) (b := b)
--       (f := fun y => Real.log y) (f' := fun x => 1 / x)
--       hderiv_uIcc h_int_one_div hcont_log_uIcc)



-- /-- Para `0 < a ≤ b`,  `∫_a^b (1/t) dt = log b - log a`. -/
-- lemma integral_one_div_eq_log_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
--     ∫ t in a..b, (1 / t) = Real.log b - Real.log a := by
--   -- derivada de log é 1/x em (0,∞), fornecida em uIcc
--   have hderiv_uIcc :
--       ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.log y) (1 / x) x := by
--     intro x hx
--     -- quando a ≤ b, uIcc a b = Icc a b
--     have hx' : x ∈ Icc a b := by
--       simpa [uIcc_of_le hab] using hx
--     have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx'.1)
--     simpa using Real.hasDerivAt_log hx0

--   -- continuidade de log em uIcc a b
--   have hcont_log_uIcc : ContinuousOn (fun y : ℝ => Real.log y) (uIcc a b) := by
--     have hIcc : ContinuousOn (fun y : ℝ => Real.log y) (Icc a b) := by
--       intro x hx
--       have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
--       simpa using (Real.continuousAt_log hx0).continuousWithinAt
--     simpa [uIcc_of_le hab] using hIcc

--   -- 1/x contínua em uIcc a b ⇒ integrável no intervalo
--   have hcont_one_div_uIcc : ContinuousOn (fun y : ℝ => 1 / y) (uIcc a b) := by
--     have hIcc : ContinuousOn (fun y : ℝ => 1 / y) (Icc a b) := by
--       have hconst : ContinuousOn (fun _ => (1 : ℝ)) (Icc a b) := continuousOn_const
--       have hid    : ContinuousOn (fun y => y) (Icc a b) := continuousOn_id
--       have h_nz : ∀ x ∈ Icc a b, x ≠ 0 := by
--         intro x hx; exact ne_of_gt (lt_of_lt_of_le ha hx.1)
--       exact hconst.div hid h_nz
--     simpa [uIcc_of_le hab] using hIcc

--   have h_int_one_div : IntervalIntegrable (fun x => 1 / x) volume a b :=
--     hcont_one_div_uIcc.intervalIntegrable

--   -- Use a versão no namespace `intervalIntegral` (aceita HasDerivAt)
--   simpa using
--     (intervalIntegral.integral_deriv_eq_sub
--       (a := a) (b := b)
--       (f := fun y => Real.log y) (f' := fun x => 1 / x)
--       hderiv_uIcc h_int_one_div hcont_log_uIcc)





-- /-- Para `0 < a ≤ b`,  `∫_a^b (1/t) dt = log b - log a`. -/
-- lemma integral_one_div_eq_log_sub {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
--     ∫ t in a..b, (1 / t) = Real.log b - Real.log a := by
--   -- derivada de log é 1/x em (0,∞), fornecida em uIcc
--   have hderiv_uIcc :
--       ∀ x ∈ uIcc a b, HasDerivAt (fun y => Real.log y) (1 / x) x := by
--     intro x hx
--     -- quando a ≤ b, uIcc a b = Icc a b (use a lemma pronta!)
--     have hx' : x ∈ Icc a b := by
--       simpa [uIcc_of_le hab] using hx
--     have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx'.1)
--     simpa using Real.hasDerivAt_log hx0

--   -- continuidade de log em uIcc a b
--   have hcont_log_uIcc : ContinuousOn (fun y : ℝ => Real.log y) (uIcc a b) := by
--     have hIcc : ContinuousOn (fun y : ℝ => Real.log y) (Icc a b) := by
--       intro x hx
--       have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le ha hx.1)
--       simpa using (Real.continuousAt_log hx0).continuousWithinAt
--     simpa [uIcc_of_le hab] using hIcc

--   -- 1/x contínua em uIcc a b ⇒ integrável no intervalo
--   have hcont_one_div_uIcc : ContinuousOn (fun y : ℝ => 1 / y) (uIcc a b) := by
--     have hIcc : ContinuousOn (fun y : ℝ => 1 / y) (Icc a b) := by
--       have hconst : ContinuousOn (fun _ => (1 : ℝ)) (Icc a b) := continuousOn_const
--       have hid    : ContinuousOn (fun y => y) (Icc a b) := continuousOn_id
--       have h_nz : ∀ x ∈ Icc a b, x ≠ 0 := by
--         intro x hx; exact ne_of_gt (lt_of_lt_of_le ha hx.1)
--       exact hconst.div hid h_nz
--     simpa [uIcc_of_le hab] using hIcc

--   have h_int_one_div : IntervalIntegrable (fun x => 1 / x) volume a b :=
--     hcont_one_div_uIcc.intervalIntegrable

--   -- TFC (versão para intervalIntegral)
--   simpa using
--     (integral_deriv_eq_sub
--       (a := a) (b := b)
--       (f := fun y => Real.log y) (f' := fun x => 1 / x)
--       hderiv_uIcc h_int_one_div hcont_log_uIcc)

/-- Para `u ≥ 1`,  `∫_1^u (1/t) dt = log u`. -/
lemma integral_one_div_from_one {u : ℝ} (hu : 1 ≤ u) :
    ∫ t in (1 : ℝ)..u, (1 / t) = Real.log u := by
  simpa [Real.log_one] using
    (integral_one_div_eq_log_sub (a := (1 : ℝ)) (b := u) (by norm_num) hu)

/-! ### Equação integral de Buchstab em [2,3] -/

/-- **Equação integral de Buchstab** para `u ∈ [2,3]`:
`u * omega u = 1 + ∫_1^{u-1} omega(t) dt`. -/
theorem buchstab_integral_equation {u : ℝ} (hu : 2 ≤ u) (hu3 : u ≤ 3) :
    u * omega u = 1 + ∫ t in (1 : ℝ)..(u - 1), omega t := by
  by_cases h : u = 2
  · -- caso base u = 2
    subst h
    have hω2 : omega 2 = 1/2 := by
      simpa using omega_eq_one_div (by norm_num) (by norm_num)
    have : (2 : ℝ) - 1 = 1 := by norm_num
    simp [hω2, this]

  · -- caso 2 < u ≤ 3
    have hgt   : 2 < u := lt_of_le_of_ne hu (ne_comm.mp h)
    have h1le  : (1 : ℝ) ≤ u - 1 := by linarith
    have h_ule2 : u - 1 ≤ 2 := by linarith
    have hpos  : 0 < u := by linarith

    -- forma explícita de ω(u) e simplificação barata (sem field_simp!)
    have hωu : omega u = (1 + Real.log (u - 1)) / u :=
      omega_eq_log_form (h1 := hgt) (h2 := hu3)



    have hL : u * omega u = 1 + Real.log (u - 1) := by
      have hu0 : u ≠ 0 := ne_of_gt hpos
      have : u * ((1 + Real.log (u - 1)) / u) = 1 + Real.log (u - 1) := by
        -- u * ((A)/u) = A, pois u ≠ 0
        field_simp [hu0]
      simpa [hωu] using this


    -- have hL : u * omega u = 1 + Real.log (u - 1) := by
    --   have hu0 : u ≠ 0 := ne_of_gt hpos
    --   -- isso fecha sem field_simp
    --   have : u * ((1 + Real.log (u - 1)) / u) = 1 + Real.log (u - 1) := by
    --     simp [div_eq_mul_inv, hu0, mul_comm, mul_left_comm, mul_assoc]
    --   simpa [hωu] using this

    -- have hL : u * omega u = 1 + Real.log (u - 1) := by
    --   have hu0 : u ≠ 0 := ne_of_gt hpos
    --   -- ((1+log(u-1))*u)/u = 1+log(u-1)
    --   have h' : ((1 + Real.log (u - 1)) * u) / u = 1 + Real.log (u - 1) :=
    --     mul_div_cancel' _ hu0
    --   -- reescreve o lado esquerdo para essa forma
    --   have : u * ((1 + Real.log (u - 1)) / u) =
    --         ((1 + Real.log (u - 1)) * u) / u := by
    --     simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    --   simpa [hωu, this] using h'

    -- em Icc(1, u-1), temos ω(t) = 1/t (pois t ≤ u-1 ≤ 2)
    have h_on_Icc : ∀ t ∈ Icc (1 : ℝ) (u - 1), omega t = 1 / t := by
      intro t ht
      have t_le_2 : t ≤ 2 := le_trans ht.2 h_ule2
      exact omega_eq_one_div ht.1 t_le_2

    -- troca integrando por 1/t; ao invés de abrir uIcc manualmente, use uIcc_of_le
    have h_int_eq :
        ∫ t in (1 : ℝ)..(u - 1), omega t
          = ∫ t in (1 : ℝ)..(u - 1), 1 / t := by
      refine integral_congr ?_
      intro t ht
      -- com 1 ≤ u-1, uIcc 1 (u-1) = Icc 1 (u-1)
      have htIcc : t ∈ Icc (1 : ℝ) (u - 1) := by
        simpa [uIcc_of_le h1le] using ht
      exact h_on_Icc t htIcc

    -- ∫ 1..(u-1) 1/t = log(u-1)
    have h_val : ∫ t in (1 : ℝ)..(u - 1), 1 / t = Real.log (u - 1) := by
      simpa using integral_one_div_from_one (u := u - 1) (hu := h1le)

    -- encadeia
    calc
      u * omega u
          = 1 + Real.log (u - 1) := hL
      _   = 1 + ∫ t in (1 : ℝ)..(u - 1), 1 / t := by rw [h_val]
      _   = 1 + ∫ t in (1 : ℝ)..(u - 1), omega t := by rw [h_int_eq]

end
