/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.External.Certs.UniformLB18794Monotonicity
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformGE18794Bridge
--import RoughBlocks.Heavy.WindowLink.BridgeLBtoPhiDiff
import RoughBlocks.Heavy.WindowLink.Block

noncomputable section
open Classical Real
open RoughBlocks

namespace RoughBlocks.Heavy

abbrev PhiDiff (m x : ℕ) : ℝ := RoughBlocks.Heavy.PhiDiffAt m x

/-! # Existência em todos os nove blocos para `m ≥ 18794` -/

def m0 : ℕ := 18794

lemma m0_ge_bridge_threshold : BridgeThreshold ≤ m0 := by decide
lemma m0_ge_2981            : 2981 ≤ m0            := by decide
lemma m0_ge_two              : 2 ≤ m0               := by decide

@[simp] lemma coe_fin9_le_eight (x : Fin 9) : (x : ℕ) ≤ 8 :=
  Nat.le_of_lt_succ x.is_lt


/-! ## Interfaces numéricas (monotonicidade e base) ------------------------ -/


/-- Lower bound analítico é de fato ≤ contagem no próprio bloco,
sem “subir” de m0: esta é a meta local certa para usar com a Ponte 2. -/
axiom LB_le_count_local
  {m x : ℕ} (hm2 : 2 ≤ m) (hx : x ≤ 8) :
  Numeric.LB m x ≤ (RoughBlocks.countRoughInBlock m x : ℝ)

theorem LB_le_PhiDiff_local
  {m x : ℕ} (hm2 : 2 ≤ m) (hx : x ≤ 8) :
  Numeric.LB m x ≤ RoughBlocks.Heavy.PhiDiffAt m x := by
  have h := LB_le_count_local (m := m) (x := x) hm2 hx
  have hEq := countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := x) hm2 hx
  simpa [RoughBlocks.Heavy.PhiDiffAt, hEq] using h


-- Antimonotonicidade de `fL` no parâmetro `m`.
axiom fL_antimono_in_m {m1 m2 : ℕ} (x : Fin 9) :
  m1 ≤ m2 →
    Numeric.fL x (Real.log (m2 : ℝ)) ≤ Numeric.fL x (Real.log (m1 : ℝ))

-- Certificado base em `m0` para todos os `x`.
axiom fL_le_margin_at_m0 (x : Fin 9) :
  Numeric.fL x (Real.log (m0 : ℝ)) ≤ Numeric.margin m0

-- Caso base certificado em `m0` para `LB ≤ count`.
axiom LB_le_countRough_at_m0 (x : ℕ) :
  Numeric.LB m0 x ≤ (RoughBlocks.countRoughInBlock m0 x : ℝ)

/-! ## Lemas numéricos principais ----------------------------------------- -/

/-! ## Passagem para `marginPaper` e para `Φ` ------------------------------ -/

/-- Para todo `m ≥ 18794`, tem-se `fL(x, log m) ≤ marginPaper(m)`.
Versão que **não** depende de `fL_le_margin_from_18794`. -/
theorem fL_le_marginPaper_general_from_18794
    (m : ℕ) (hm : m0 ≤ m) :
    ∀ (x : Fin 9),
      Numeric.fL x (Real.log (m : ℝ)) ≤ Numeric.marginPaper m := by
  intro x
  -- fL(m) ≤ fL(m0)
  have hF_antimono :
      Numeric.fL x (Real.log (m : ℝ))
        ≤ Numeric.fL x (Real.log (m0 : ℝ)) :=
    fL_antimono_in_m (x := x) (m1 := m0) (m2 := m) hm
  -- fL(m0) ≤ margin(m0)
  have h_base : Numeric.fL x (Real.log (m0 : ℝ)) ≤ Numeric.margin m0 :=
    fL_le_margin_at_m0 x
  -- margin(m0) ≤ marginPaper(m0)
  have h_toPaper0 : Numeric.margin m0 ≤ Numeric.marginPaper m0 :=
    Numeric.margin_le_marginPaper_of_ge_two m0_ge_2981
  -- marginPaper(m0) ≤ marginPaper(m)
  have h_paperMono : Numeric.marginPaper m0 ≤ Numeric.marginPaper m :=
    Numeric.marginPaper_mono_from_18794
      (hm := m0_ge_bridge_threshold) (hmn := hm)
  exact hF_antimono.trans (h_base.trans (h_toPaper0.trans h_paperMono))

/-- Para todo `m ≥ 18794`, tem-se `LB(m,x) ≤ Φ(m,x)` (Φ = nosso `PhiDiff`). -/
theorem LB_le_PhiDiff_general_from_18794
    (m : ℕ) (hm : m0 ≤ m) :
    ∀ (x : Fin 9),
      Numeric.LB m ↑x ≤ PhiDiff m ↑x := by
  intro x
  -- hipóteses “curtas”
  have hm2 : 2 ≤ m := m0_ge_two.trans hm
  have hx  : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.is_lt
  -- aplica a versão local e reescreve o alvo com a nossa abreviação PhiDiff
  have h := LB_le_PhiDiff_local (m := m) (x := (x : ℕ)) hm2 hx
  simpa [PhiDiff, RoughBlocks.Heavy.PhiDiffAt] using h

/-! ## Forma requerida pelo certificado externo ---------------------------- -/

-- Certificado externo: para `m ≥ m0`, tem-se `External.Certs.fL x (log m) ≤ margin m`.
axiom fL_external_le_margin_from_18794 :
  ∀ {m : ℕ}, m0 ≤ m →
    (∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m)

/-- Forma exigida pelo teorema externo. -/
lemma fL_cert_le_margin_from_18794 (m : ℕ) (hm : m0 ≤ m) :
  ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m :=
  fL_external_le_margin_from_18794 hm


/-- As `PhiDiffAt` coincidem por definição. -/
lemma PhiDiff_heavy_eq_certs (m x : ℕ) :
  PhiDiff m x = External.Certs.PhiDiffAt m x := rfl

/-- **Família `hL` pronta**: para `m ≥ m0`, temos
`Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ)` para todo `x`. -/
def hL_family (m : ℕ) (hm : m0 ≤ m) :
  ∀ x : Fin 9,
    Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ) :=
by
  intro x
  -- seu lema global já dá `LB ≤ PhiDiff` na versão Heavy…
  have h := LB_le_PhiDiff_general_from_18794 m hm x
  -- …e aqui reescrevemos para a versão `External.Certs`.
  simpa [PhiDiff, PhiDiff_heavy_eq_certs m (x : ℕ)] using h


-- (útil para fechar cadeias ≤ sem reescrever o enunciado)
lemma PhiDiff_heavy_le_certs (m x : ℕ) :
  PhiDiff m x ≤ External.Certs.PhiDiffAt m x := by
  simp [PhiDiff_heavy_eq_certs m x]

/-! ## Teorema principal --------------------------------------------------- -/

/-- Para todo `m ≥ 18794` e todo `x ∈ {0,…,8}`, existe um número *m-áspero*
no bloco `K(m, x)`. -/
theorem exists_mRough_from_18794
    {m : ℕ} (hm : m0 ≤ m) (x : Fin 9) :
    ∃ k ∈ K m ↑x, mRough m k := by
  -- Pré-condições do teorema certificado externo
  have hBridge : BridgeThreshold ≤ m := m0_ge_bridge_threshold.trans hm
  have hm_ext : External.Certs.m0 ≤ m := by
    have : External.Certs.m0 = m0 := by decide
    simpa [this] using hm
  -- Famílias de hipóteses (para todos x)
  have hF : ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m :=
    fL_cert_le_margin_from_18794 m hm
  -- Primeiro provamos a versão com o nosso Φ e reescrevemos para `External.Certs`
  have hL_num := LB_le_PhiDiff_general_from_18794 m hm
  have hL : ∀ x : Fin 9, Numeric.LB m ↑x ≤ External.Certs.PhiDiffAt m ↑x := by
    intro x
    -- reescreve RHS via igualdade `rfl` das definições de PhiDiff
    simpa [PhiDiff_heavy_eq_certs m (x : ℕ)] using (hL_num x)
  -- Assinatura: `hBridge`, `hm_ext`, `hF`, `hL`, `x`
  exact RoughBlocks.External.Certs.exists_mRough_in_allNine_from_18794
    hBridge hm_ext hF hL x

/-! ## Sanity checks ------------------------------------------------------- -/

#print axioms exists_mRough_from_18794
#check exists_mRough_from_18794

end RoughBlocks.Heavy
