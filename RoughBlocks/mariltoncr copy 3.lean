/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Heavy.Bridge
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Buchstab.Core
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Monotonicity
import RoughBlocks.Heavy.WindowLink.BridgeLBtoPhiDiff
import RoughBlocks.Heavy.WindowLink.Bridge_fL_to_Margin

noncomputable section
open Classical Real
open RoughBlocks

namespace RoughBlocks.Heavy

/-! # Existência em todos os nove blocos para `m ≥ 18794`

Esta versão remove axiomas antigos e centraliza a prova em três pilares:
1. **Janela (Heavy.WindowLink.Block)** para identificar contagem ↔ Φ.
2. **Núcleo de Buchstab (Heavy.Buchstab.Core)** para `LB ≤ Φ_GE` local.
3. **Framework externo** para encadear `fL ≤ margin ≤ LB ≤ Φ` quando for preciso.

O único ponto ainda aberto está marcado como `admit`: é a chamada concreta ao
lema do núcleo que dá `LB ≤ Φ_GE` no próprio `m` e bloco `x`.
-/

abbrev PhiDiff (m x : ℕ) : ℝ := RoughBlocks.Heavy.PhiDiffAt m x

/-- Ponto de partida do projeto. -/
def m0 : ℕ := 18794

lemma m0_ge_bridge_threshold : BridgeThreshold ≤ m0 := by decide
lemma m0_ge_two              : 2 ≤ m0               := by decide

@[simp] lemma coe_fin9_le_eight (x : Fin 9) : (x : ℕ) ≤ 8 :=
  Nat.le_of_lt_succ x.is_lt

 theorem LB_le_count_local
  {m x : ℕ} (hm2 : 2 ≤ m) (hx : x ≤ 8) :
  Numeric.LB m x ≤ (RoughBlocks.countRoughInBlock m x : ℝ) := by
  -- prova pronta no Bridge: LB ≤ countRoughInBlock, sob 2 ≤ m e x ≤ 8
  simpa using LB_le_count_block (m := m) (x := x) hm2 hx

/-- Versão direta: `LB ≤ Φ` no `Heavy` via Ponte 2. -/
theorem LB_le_PhiDiff_local
  {m x : ℕ} (hm2 : 2 ≤ m) (hx : x ≤ 8) :
  Numeric.LB m x ≤ RoughBlocks.Heavy.PhiDiffAt m x := by
  -- você ainda precisa de `LB ≤ count` local (o gancho do núcleo)
  have hLBcount : Numeric.LB m x ≤ (RoughBlocks.countRoughInBlock m x : ℝ) :=
    LB_le_count_local hm2 hx
  -- chama a Ponte 2 (já pronta no arquivo que você mostrou)
  exact RoughBlocks.Heavy.LB_le_PhiDiff hm2 hx hLBcount


/-- Forma em `Fin 9` e `m ≥ m0`. -/
theorem LB_le_PhiDiff_general_from_18794
    (m : ℕ) (hm : m0 ≤ m) :
    ∀ (x : Fin 9),
      Numeric.LB m ↑x ≤ PhiDiff m ↑x := by
  intro x
  have hm2 : 2 ≤ m := m0_ge_two.trans hm
  have hx  : (x : ℕ) ≤ 8 := coe_fin9_le_eight x
  have h := LB_le_PhiDiff_local (m := m) (x := (x : ℕ)) hm2 hx
  simpa [PhiDiff, RoughBlocks.Heavy.PhiDiffAt] using h

/-!
## 2) Ponte com o certificado externo

As `PhiDiffAt` de `Heavy` e do módulo `External.Certs` são defeq.
-/

lemma PhiDiff_heavy_eq_certs (m x : ℕ) :
  PhiDiff m x = External.Certs.PhiDiffAt m x := rfl

lemma PhiDiff_heavy_le_certs (m x : ℕ) :
  PhiDiff m x ≤ External.Certs.PhiDiffAt m x := by
  simpa [PhiDiff_heavy_eq_certs m x]

/-!
## 3) Teorema principal (forma “framework”: recebe `fL ≤ margin` como hipótese)
-/

/-- Para todo `m ≥ 18794` e todo `x ∈ {0,…,8}`, existe um número *m-áspero*
no bloco `K(m, x)` — assumindo a família `fL ≤ margin` (que virá do bridge GE).
-/
theorem exists_mRough_from_18794
    {m : ℕ} (hm : m0 ≤ m)
    (hF : ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m)
    (x : Fin 9) :
    ∃ k ∈ K m ↑x, mRough m k := by
  -- Pré-condições do teorema certificado externo
  have hBridge : BridgeThreshold ≤ m := m0_ge_bridge_threshold.trans hm
  have hm_ext : External.Certs.m0 ≤ m := by
    have : External.Certs.m0 = m0 := by decide
    simpa [this] using hm
  -- Parte `LB ≤ Φ` em `Heavy` e reescrita para `External.Certs`
  have hL_num := LB_le_PhiDiff_general_from_18794 m hm
  have hL :
      ∀ x : Fin 9, Numeric.LB m ↑x ≤ External.Certs.PhiDiffAt m ↑x := by
    intro x
    -- As duas definições de PhiDiffAt coincidem por defeq
    simpa [PhiDiff_heavy_eq_certs m (x : ℕ)] using (hL_num x)
  -- Assinatura: `hBridge`, `hm_ext`, `hF`, `hL`, `x`
  exact RoughBlocks.External.Certs.exists_mRough_in_allNine_from_18794
    hBridge hm_ext hF hL x

/-- Versão “para uso diário”: de `fL ≤ margin` + `margin ≤ marginPaper` + `LB ≤ count`
sai `fL ≤ PhiDiffAt` para todo `x`, quando `m` está na faixa formal. -/
lemma fL_le_PhiDiff_general_from_bridge
  {m : ℕ} (hmB : BridgeThreshold ≤ m) (hm2 : 2 ≤ m)
  (hmargin_le_marginPaper : RoughBlocks.Heavy.Numeric.margin m
                            ≤ RoughBlocks.Heavy.Numeric.marginPaper m)
  (hF : ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ))
                     ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hLBcount : ∀ x : Fin 9,
                RoughBlocks.Heavy.Numeric.LB m (x : ℕ)
                ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ)) :
  ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ RoughBlocks.Heavy.PhiDiffAt m (x : ℕ) := by
  intro x
  -- 1) fL ≤ marginPaper
  have hLocal :
      External.Certs.fL x (Real.log (m : ℝ))
        ≤ RoughBlocks.Heavy.Numeric.marginPaper m :=
    RoughBlocks.Heavy.fL_le_marginPaper_from_18794
      (External.Certs.fL) hmB x (hF x) hmargin_le_marginPaper
  -- 2) Ponte completa: fL ≤ marginPaper ≤ LB ≤ PhiDiffAt
  exact RoughBlocks.Heavy.fL_log_le_PhiDiff_from_bridge
    (External.Certs.fL) hmB hm2 x hLocal (hLBcount x)


/-! ## Sanity checks ------------------------------------------------------- -/

#print axioms exists_mRough_from_18794
#check exists_mRough_from_18794

end RoughBlocks.Heavy
