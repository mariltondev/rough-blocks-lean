/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 ...
-/

import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Light.Native.Compute18794
import RoughBlocks.External.Certs.UniformLB18794Bridge
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformLB18794Monotonicity

namespace RoughBlocks.MainResults

open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs

/-- Ramo grande: `m ≥ BridgeThreshold` dá existência em todos os 9 níveis,
    assumindo as duas desigualdades ponto-a-ponto (mesmas do seu teorema). -/
theorem big_range_allNine
  (hm0B :
    m0 ≤ BridgeThreshold)
  (hF_all :
    ∀ {m : ℕ}, BridgeThreshold ≤ m →
      ∀ x : Fin 9, fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hL_all :
    ∀ {m : ℕ}, BridgeThreshold ≤ m →
      ∀ x : Fin 9, RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  ∀ m, BridgeThreshold ≤ m → ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
  intro m hB x
  have hm0 : m0 ≤ m := hm0B.trans hB
  exact exists_mRough_in_allNine_from_18794
          (m := m) hB hm0 (hF_all hB) (hL_all hB) x

/-- Cola final: (i) ramo grande proposicional + (ii) verificação booleana até 18794. -/
theorem existence_main_all
  (hm0B :
    m0 ≤ BridgeThreshold)
  (hF_all :
    ∀ {m : ℕ}, BridgeThreshold ≤ m →
      ∀ x : Fin 9, fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hL_all :
    ∀ {m : ℕ}, BridgeThreshold ≤ m →
      ∀ x : Fin 9, RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  (∀ m, BridgeThreshold ≤ m → ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k)
  ∧ (RoughBlocks.Light.Native.verify2_18794 = true) := by
  exact ⟨big_range_allNine hm0B hF_all hL_all,
         RoughBlocks.Light.Native.verify2_18794_true⟩

-- Se você já tem lemas globais com esses nomes (ou equivalentes),
-- dá pra fechar sem hipóteses:
-- theorem existence_main_all_noHyp :
--   (∀ m, BridgeThreshold ≤ m → ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k)
--   ∧ (RoughBlocks.Light.Native.verify2_18794 = true) :=
--   existence_main_all
--     (hm0B := by decide)             -- se de fato m0 ≤ BridgeThreshold é decidível no seu setup
--     (hF_all := fL_le_margin_all)    -- o seu lema global para fL ≤ margin
--     (hL_all := LB_le_PhiDiff_all)   -- o seu lema global para LB ≤ PhiDiffAt

end RoughBlocks.MainResults
