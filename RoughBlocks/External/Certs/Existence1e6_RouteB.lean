/-
SPDX-License-Identifier: Apache-2.0
(c) 2025 Marilton Costa Ribeiro
-/

import Mathlib
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Bridge
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.Heavy.Log10Bounds
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.Bridge
import RoughBlocks.Heavy.WindowLink.Block  -- count ↔ Φ na janela curta

namespace RoughBlocks.External.Certs
noncomputable section
open Classical Real
open RoughBlocks
open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs
open RoughBlocks.External.Certs.UniformLB18794Bridge
open RoughBlocks.External.Certs.UniformGE18794Bridge

/-- Atalho: Φ-dif na janela curta (camada Heavy). -/
abbrev PhiDiffAt (m x : ℕ) : ℝ := RoughBlocks.Heavy.PhiDiffAt m x

/-! ## 1) Bound leve na faixa 10^6 --------------------------------------- -/

/-- Para `m ≥ 10^6` e `x ≤ 8`, temos `LB m x ≥ 1`. -/
theorem main_theorem_ge_1e6 {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
  RoughBlocks.Heavy.Numeric.LB m x ≥ 1 :=
  RoughBlocks.Heavy.Numeric.budget_conservative_formal (m := m) (x := x) hm hx

/-- Forma “ranges” (quantificada). -/
theorem main_theorem_ge_1e6_ranges :
  ∀ {m}, 1_000_000 ≤ m → ∀ {x}, x ≤ 8 → RoughBlocks.Heavy.Numeric.LB m x ≥ 1 := by
  intro m hm x hx
  exact main_theorem_ge_1e6 (m := m) (x := x) hm hx

/-! ## 2) De `LB ≤ Φ` para `LB ≤ count` (via `count = Φ`) ----------------- -/

/-- Para `m ≥ 10^6`, se `LB ≤ PhiDiffAt`, então também `LB ≤ countRoughInBlock`. -/
theorem hLBleCount_from_PhiDiff_ge_1e6
  {m : ℕ} (hm : 1_000_000 ≤ m)
  (hLBlePhi : ∀ x : Fin 9,
      RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  ∀ x : Fin 9,
      RoughBlocks.Heavy.Numeric.LB m (x : ℕ)
        ≤ (countRoughInBlock m (x : ℕ) : ℝ) := by
  intro x
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ 1_000_000) hm
  have hx  : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.is_lt
  have hEq := RoughBlocks.Heavy.countRoughInBlock_eq_phiDiff_succ_real
                (m := m) (x := (x : ℕ)) hm2 hx
  simpa [hEq, PhiDiffAt] using (hLBlePhi x)

/-! ## 3) Existência por bloco e ∀x para `m ≥ 10^6` ---------------------- -/

/-- Versão “por bloco”: com `m ≥ 10^6` e `LB ≤ count`, há um m-áspero em `K(m,x)`. -/
theorem exists_mRough_ge_1e6_allNine
  {m : ℕ} (hm : 1_000_000 ≤ m) (x : Fin 9)
  (hLBleCount :
     RoughBlocks.Heavy.Numeric.LB m (x : ℕ)
       ≤ (countRoughInBlock m (x : ℕ) : ℝ)) :
  ∃ k ∈ K m (x : ℕ), mRough m k := by
  -- (1) LB(m,x) ≥ 1
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.is_lt
  have hLB_ge1 : RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≥ 1 :=
    main_theorem_ge_1e6_ranges (m := m) hm (x := x) hx
  -- (2) 1 ≤ LB ≤ count ⇒ 1 ≤ count (em ℝ)
  have h1_le_count_real :
      (1 : ℝ) ≤ (countRoughInBlock m (x : ℕ) : ℝ) :=
    le_trans (by simpa using hLB_ge1) hLBleCount
  -- (3) sobe para ℕ e extrai testemunha
  have hcount_ge1_nat :
      1 ≤ countRoughInBlock m (x : ℕ) := by exact_mod_cast h1_le_count_real
  have hpos :
      0 < ((K m (x : ℕ)).filter (mRough m)).card := by
    have : 0 < countRoughInBlock m (x : ℕ) := Nat.succ_le.mp hcount_ge1_nat
    simpa [countRoughInBlock] using this
  rcases (Finset.card_pos.mp hpos) with ⟨k, hk⟩
  rcases (Finset.mem_filter.mp hk) with ⟨hkK, hkR⟩
  exact ⟨k, hkK, hkR⟩

/-- Versão “∀x”: `m ≥ 10^6` e família `LB ≤ count` ⇒ em cada bloco existe m-áspero. -/
theorem exists_mRough_ge_1e6_allNine_forall
  {m : ℕ} (hm : 1_000_000 ≤ m)
  (hLBleCount :
    ∀ x : Fin 9,
      RoughBlocks.Heavy.Numeric.LB m (x : ℕ)
        ≤ (countRoughInBlock m (x : ℕ) : ℝ)) :
  ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
  intro x
  exact exists_mRough_ge_1e6_allNine hm x (hLBleCount x)

/-! ## 4) “Rota B” direta a partir de `LB ≤ Φ` ---------------------------- -/

/-- “Rota B” por bloco: basta `m ≥ 10^6` e a família `LB ≤ Φ`. -/
theorem exists_mRough_ge_1e6_allNine_via_Phi
  {m : ℕ} (hm : 1_000_000 ≤ m)
  (hLBlePhi : ∀ x : Fin 9,
      RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ))
  (x : Fin 9) :
  ∃ k ∈ K m (x : ℕ), mRough m k :=
  exists_mRough_ge_1e6_allNine hm x
    ((hLBleCount_from_PhiDiff_ge_1e6 hm hLBlePhi) x)

/-- “Rota B” ∀x: basta `m ≥ 10^6` e a família `LB ≤ Φ`. -/
theorem exists_mRough_ge_1e6_allNine_forall_via_Phi
  {m : ℕ} (hm : 1_000_000 ≤ m)
  (hLBlePhi : ∀ x : Fin 9,
      RoughBlocks.Heavy.Numeric.LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ)) :
  ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
  intro x
  exact exists_mRough_ge_1e6_allNine_via_Phi hm hLBlePhi x


#print axioms RoughBlocks.External.Certs.exists_mRough_ge_1e6_allNine_forall
#check RoughBlocks.External.Certs.exists_mRough_ge_1e6_allNine_forall


end
end RoughBlocks.External.Certs
