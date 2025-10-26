/-
SPDX-License-Identifier: Apache-2.0

Parte 4 — Montagem final (existência em cada bloco), versão enxuta.

Dependências:
- Parte 01: fatos estáticos (U0Default ≤ BridgeThreshold ≤ m0, 2 ≤ m0, uniformLB>1)
- Parte 02: definições LB/margin (não usadas diretamente aqui)
- Parte 03: (opcional) pode fornecer o "plug" Hplug abaixo a partir do JSON

Esta versão não usa `Numeric` nem `fL`/`vL`/`rows`.
-/

import Mathlib
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.WindowLink.Block

--import RoughBlocks.External.Certs.Parte01
--import RoughBlocks.External.Certs.Parte02
--import RoughBlocks.External.Certs.Parte03
import RoughBlocks.External.Certs.UniformLB18794Bridge

namespace RoughBlocks.External.Certs
noncomputable section

open Classical Real
open RoughBlocks.Heavy
open RoughBlocks.External.Certs.UniformLB18794Bridge

/-- Se `m0 ≤ m`, então `U0Default ≤ m`
    (usa Parte 01: `U0Default ≤ BridgeThreshold ≤ m0`). -/
lemma U0Default_le_of_ge_m0 {m : ℕ}
    (hU0B : U0Default ≤ BridgeThreshold) (hB0 : BridgeThreshold ≤ m0) (hm : m0 ≤ m) :
    U0Default ≤ m :=
  le_trans (le_trans hU0B hB0) hm

/-- Se `m0 ≤ m`, então `2 ≤ m` (usa Parte 01: `2 ≤ m0`). -/
lemma two_le_of_ge_m0 {m : ℕ} (h2m0 : 2 ≤ m0) (hm : m0 ≤ m) : 2 ≤ m :=
  le_trans h2m0 hm

/-!
`Hplug` é a única hipótese “externa” que precisamos aqui: para todo `m ≥ m0`
e todo bloco `x ≤ 8`, o lower bound uniforme (tabela) é ≤ `PhiDiffAt m x`.
Você pode produzi-la a partir do seu verificador (Parte 03/JSON), ou pela
cadeia analítica (rows ≤ … ≤ Φ) quando ela estiver disponível.
-/

/-- Versão existencial “1 por bloco”, para todo `m ≥ m0`, usando apenas
o plug `uniformLB ≤ Φ` e a tabela `uniformLB>1` da Parte 01. -/
theorem exists_allNine_ge_m0_using_plug
    (h2m0 : 2 ≤ m0)
    -- Parte 01: tabela computacional `uniformLB(x) > 1`
    (hUB1 : ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1)
    -- Plug que vem do verificador/cadeia: `uniformLB ≤ Φ` para todo `m ≥ m0`
    (Hplug : ∀ {m : ℕ}, m0 ≤ m → ∀ x : Fin 9,
              (uniformLB18794_finalLowerLo x : ℝ) ≤ PhiDiffAt m (x : ℕ))
    {m : ℕ} (hm : m0 ≤ m) (x : Fin 9) :
    ∃ k ∈ K m (x : ℕ), mRough m k := by
  -- 1) Φ(m,x) ≥ uniformLB(x) > 1
  have hPhi_ge_ULB :
      PhiDiffAt m (x : ℕ) ≥ (uniformLB18794_finalLowerLo x : ℝ) := Hplug hm x
  have hPhi_gt1 : (1 : ℝ) < PhiDiffAt m (x : ℕ) :=
    lt_of_lt_of_le (hUB1 x) hPhi_ge_ULB
  -- 2) Φ = contagem no bloco ⇒ existe 1-áspero
  have hx  : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  have hm2 : 2 ≤ m := two_le_of_ge_m0 h2m0 hm
  have hEq := countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := (x : ℕ)) hm2 hx
  have hcount_gt1 : 1 < countRoughInBlock m (x : ℕ) := by
    have : (1 : ℝ) < (countRoughInBlock m (x : ℕ) : ℝ) := by simpa [hEq] using hPhi_gt1
    exact_mod_cast this
  have hpos : 0 < ((K m (x : ℕ)).filter (mRough m)).card := by
    exact Nat.lt_trans (by decide : 0 < 1) hcount_gt1
  rcases (Finset.card_pos.mp hpos) with ⟨k, hk⟩
  rcases (Finset.mem_filter.mp hk) with ⟨hkK, hkR⟩
  exact ⟨k, hkK, hkR⟩

#print axioms RoughBlocks.External.Certs.exists_allNine_ge_m0_using_plug
#check RoughBlocks.External.Certs.exists_allNine_ge_m0_using_plug


/-- Corolário “1 por bloco”: `card ≥ 1`. -/
theorem one_per_block_ge_m0_using_plug
    (h2m0 : 2 ≤ m0)
    (hUB1 : ∀ x : Fin 9, (uniformLB18794_finalLowerLo x : ℝ) > 1)
    (Hplug : ∀ {m : ℕ}, m0 ≤ m → ∀ x : Fin 9,
              (uniformLB18794_finalLowerLo x : ℝ) ≤ PhiDiffAt m (x : ℕ))
    {m : ℕ} (hm : m0 ≤ m) (x : Fin 9) :
    1 ≤ ((K m (x : ℕ)).filter (mRough m)).card := by
  rcases exists_allNine_ge_m0_using_plug h2m0 hUB1 Hplug hm x with ⟨k, hkK, hkR⟩
  have : 0 < ((K m (x : ℕ)).filter (mRough m)).card :=
    Finset.card_pos.mpr ⟨k, by simpa [Finset.mem_filter] using ⟨hkK, hkR⟩⟩
  exact Nat.succ_le_of_lt this


#print axioms RoughBlocks.External.Certs.one_per_block_ge_m0_using_plug
#check RoughBlocks.External.Certs.one_per_block_ge_m0_using_plug


end
end RoughBlocks.External.Certs
