/-
SPDX-License-Identifier: Apache-2.0
Part of the RoughBlocks project.
-/
import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.BridgeLBtoPhiDiff

namespace RoughBlocks.Heavy
open Real
open RoughBlocks.Heavy.Numeric

/-! ## (1) Versão genérica (adapter de transitividade) -/
theorem fL_le_marginPaper_from_18794
  (fL : Fin 9 → ℝ → ℝ)
  {m : ℕ} (_hm : BridgeThreshold ≤ m) (x : Fin 9)
  (hfL_le_margin : fL x (Real.log (m : ℝ)) ≤ margin m)
  (hmargin_le_marginPaper : margin m ≤ marginPaper m) :
  fL x (Real.log (m : ℝ)) ≤ marginPaper m := by
  exact hfL_le_margin.trans hmargin_le_marginPaper

/-! ## (2) Ponte 1 completa: `fL ≤ marginPaper ≤ LB ≤ PhiDiffAt` -/
theorem fL_log_le_PhiDiff_from_bridge
  (fL : Fin 9 → ℝ → ℝ)
  {m : ℕ} (hm : BridgeThreshold ≤ m) (hm2 : 2 ≤ m) (x : Fin 9)
  (hLocal   : fL x (Real.log (m : ℝ)) ≤ marginPaper m)
  (hLBcount : LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ)) :
  fL x (Real.log (m : ℝ)) ≤ PhiDiffAt m (x : ℕ) := by
  -- x ≤ 8
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.is_lt
  -- U0Default ≤ m (pois BridgeThreshold ≥ U0Default)
  have hU0 : U0Default ≤ m := le_trans (by decide : U0Default ≤ BridgeThreshold) hm
  -- marginPaper ≤ LB (degrau analítico com 1/2 em [2,3])
  have h_mid : marginPaper m ≤ LB m (x : ℕ) :=
    (LB_ge_marginPaper (m := m) (x := (x : ℕ)) hU0 hx)
  -- LB ≤ PhiDiffAt (Ponte 2)
  have h_tail : LB m (x : ℕ) ≤ PhiDiffAt m (x : ℕ) :=
    LB_le_PhiDiff (m := m) (x := (x : ℕ)) hm2 hx hLBcount
  -- encadeia
  exact hLocal.trans (h_mid.trans h_tail)

end RoughBlocks.Heavy
