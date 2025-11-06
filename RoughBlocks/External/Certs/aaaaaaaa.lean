import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Basic
import RoughBlocks.External.Certs.aROTA_B_01

open scoped Interval
open MeasureTheory intervalIntegral

set_option maxHeartbeats 500000 in
example : True := by
  let g : ℝ → ℝ := fun x => x ^ 2
  let g' : ℝ → ℝ := fun x => 2 * x
  let A_y : ℕ → ℝ → ℝ := fun _ _ => 1

  have h :=
    abel_block_partition_neg g g' A_y
      1 2 2
      (by decide) (by decide) (by decide)
      (by
        intro n hn t ht
        have : HasDerivAt (fun x : ℝ => x ^ 2) (2 * t) t := by
          simpa using (hasDerivAt_pow 2 t)
        simpa [g, g'] using this)
      (by
        intro n hn
        have : IntervalIntegrable (fun t => 2 * t) (μ := volume)
            (1 + ↑n) (1 + ↑n + 1) :=
          intervalIntegral.intervalIntegrable_id.const_mul (c := 2)
        simpa [g'] using this)
      (by
        intro n hn t ht
        simp [A_y])

  exact True.intro
