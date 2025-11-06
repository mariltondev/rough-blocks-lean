/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Monotonicity
import RoughBlocks.External.BridgeFromCert18794
import RoughBlocks.External.Certs.FullVerifier
import RoughBlocks.Heavy.WindowLink.BridgeLBtoPhiDiff
import RoughBlocks.Heavy.WindowLink.Bridge_fL_to_Margin

noncomputable section
open Classical Real
open RoughBlocks

namespace RoughBlocks.Heavy

/-- Parâmetro-alvo do projeto. -/
def m0 : ℕ := 18794

lemma m0_ge_bridge_threshold : BridgeThreshold ≤ m0 := by decide
lemma m0_ge_two              : 2 ≤ m0               := by decide
lemma m0_ge_2981             : 2981 ≤ m0            := by decide

@[simp] lemma coe_fin9_le_eight (x : Fin 9) : (x : ℕ) ≤ 8 :=
  Nat.le_of_lt_succ x.is_lt

/-- Atalho: a `PhiDiffAt` do `Heavy`. -/
abbrev PhiDiff (m x : ℕ) : ℝ := RoughBlocks.Heavy.PhiDiffAt m x

/-! ## 1) Identidade `Heavy` ↔ `External.Certs` -/

lemma PhiDiff_heavy_eq_certs (m x : ℕ) :
  PhiDiff m x = External.Certs.PhiDiffAt m x := rfl

lemma PhiDiff_heavy_le_certs (m x : ℕ) :
  PhiDiff m x ≤ External.Certs.PhiDiffAt m x := by
  simp [PhiDiff_heavy_eq_certs m x]

/-! ## 2) Lema útil: margin ≤ marginPaper para m ≥ m0 --------------------- -/
lemma margin_le_marginPaper_from_18794 (m : ℕ) (hm : m0 ≤ m) :
  Numeric.margin m ≤ Numeric.marginPaper m := by
  -- precisa de 2981 ≤ m (apesar do nome do lemma base)
  have hm2981 : 2981 ≤ m := le_trans m0_ge_2981 hm
  exact Numeric.margin_le_marginPaper_of_ge_two hm2981

/-! ## 3) Teorema principal (forma framework, consumindo hF e hL) ---------- -/

/-- **Existência para `m ≥ 18794` nos 9 blocos** (forma framework).

Entradas:
* `hF`: família computacional `External.Certs.fL x (log m) ≤ Numeric.margin m`;
* `hL`: família analítica `Numeric.LB m x ≤ External.Certs.PhiDiffAt m x`.

Saída: existe um `m`-áspero em `K(m, x)` para cada bloco `x`.
-/
theorem exists_mRough_from_18794
    {m : ℕ} (hm : m0 ≤ m)
    (hF : ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m)
    (hL : ∀ x : Fin 9, Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ))
    (x : Fin 9) :
    ∃ k ∈ K m (x : ℕ), mRough m k := by
  -- Pré-condições formais do teorema externo
  have hBridge : BridgeThreshold ≤ m := m0_ge_bridge_threshold.trans hm
  have hm_ext : External.Certs.m0 ≤ m := by
    have : External.Certs.m0 = m0 := by decide
    simpa [this] using hm
  -- Chamada direta ao teorema externo “all nine”
  exact RoughBlocks.External.Certs.exists_mRough_in_allNine_from_18794
    hBridge hm_ext hF hL x

/-! ## 4) Helpers (se quiser derivar hL a partir de LB ≤ count) ------------- -/

lemma hL_family_from_LB_count
    {m : ℕ} (hm : m0 ≤ m)
    (hLBcount :
      ∀ x : Fin 9,
        Numeric.LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ)) :
    ∀ x : Fin 9,
      Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ) := by
  intro x
  have hm2 : 2 ≤ m := m0_ge_two.trans hm
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.is_lt
  -- ponte 2 já pronta no módulo WindowLink
  have h :=
    RoughBlocks.Heavy.LB_le_PhiDiff (m := m) (x := (x : ℕ)) hm2 hx (hLBcount x)
  simpa [PhiDiff_heavy_eq_certs m (x : ℕ)] using h

/-- Família `LB ≤ count` produzida diretamente pelo certificado. -/
lemma hLBcount_from_certificate
    (m : ℕ) (hm : m0 ≤ m) :
    ∀ x : Fin 9,
      Numeric.LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ) := by
  intro x
  -- recibo completo já verificado → igualdade a true
  have hcert :
    RoughBlocks.External.Certs.FullVerifier.verify_full_certificate = true :=
    RoughBlocks.External.Certs.FullVerifier.full_certificate_is_valid
  have hm₀ : (18794 : ℕ) ≤ m := by simpa [m0] using hm
  have hx : (x : ℕ) ≤ 8 := coe_fin9_le_eight x
  simpa using
    RoughBlocks.External.bridge_ge_18794_from_verified_certificate hcert hm₀ hx

/-- Família `LB ≤ PhiDiffAt` derivada automaticamente do certificado uniforme. -/
lemma hL_family_from_certificate
    (m : ℕ) (hm : m0 ≤ m) :
    ∀ x : Fin 9,
      Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ) :=
  hL_family_from_LB_count (m := m) hm (hLBcount_from_certificate m hm)

/-- Variante prática: parte apenas de `hLBcount` para construir `hL`
    e instanciar o teorema externo. -/
theorem exists_mRough_from_18794_of_LB_count
    {m : ℕ} (hm : m0 ≤ m)
    (hF : ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m)
    (hLBcount :
      ∀ x : Fin 9,
        Numeric.LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ))
    (x : Fin 9) :
    ∃ k ∈ K m (x : ℕ), mRough m k := by
  have hL := hL_family_from_LB_count (m := m) hm hLBcount
  exact exists_mRough_from_18794 hm hF hL x

/-! ## 5) Sanity ----------------------------------------------------------- -/

#print axioms exists_mRough_from_18794
#check exists_mRough_from_18794

end RoughBlocks.Heavy
