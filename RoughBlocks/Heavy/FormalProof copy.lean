/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.Buchstab  -- ω(u) e ω(u)=1/u em [1,2]

noncomputable section
open Real
open RoughBlocks.Heavy

namespace RoughBlocks.Heavy.Buchstab.SieveX0

/-- Núcleo de Buchstab (x=0) na janela curta, em forma direta.
Centralizado aqui: **prove isto** no seu stack analítico (sem `sorry`) e
todo o pipeline fecha para `x=0`. -/
axiom core_lower_bound_x0
  {m : ℕ} (hm : 2 ≤ m) :
  ((PhiGE (m*m + 0*m + m) (m+1) : ℝ) - (PhiGE (m*m + 0*m) (m+1) : ℝ))
    ≥ (m : ℝ) / Real.log m *
        RoughBlocks.Heavy.Buchstab.omega
          (Real.log ((m*m + 0*m : ℕ) : ℝ) / Real.log m)
      - (Numeric.C1Default : ℝ) * ((m : ℝ) / (Real.log m)^2)
      - (Numeric.C2Default : ℝ)

/-- **Lema local (x=0) usado pelo wrapper.**
Ele simplesmente expõe o bound do núcleo (acima) com a mesma assinatura. -/
theorem local_window_x0_lower_bound
  {m : ℕ} (hm : 2 ≤ m) :
  ((PhiGE (m*m + 0*m + m) (m+1) : ℝ) - (PhiGE (m*m + 0*m) (m+1) : ℝ))
    ≥ (m : ℝ) / Real.log m *
        RoughBlocks.Heavy.Buchstab.omega
          (Real.log ((m*m + 0*m : ℕ) : ℝ) / Real.log m)
      - (Numeric.C1Default : ℝ) * ((m : ℝ) / (Real.log m)^2)
      - (Numeric.C2Default : ℝ) := by
  exact core_lower_bound_x0 hm

end RoughBlocks.Heavy.Buchstab.SieveX0

/-- **Wrapper final (Opção A): Φ-dif ≥ LB em x=0, para `m ≥ 1e6`.**
Depende de:
* `local_window_x0_lower_bound` (Buchstab x=0 na janela curta);
* `ω(2)=1/2` e `log(m^2)/log m = 2`;
* definição de `Numeric.LB` para `x=0`. -/
lemma PhiDiff_x0_ge_LB_from_1e6
  {m : ℕ} (hm : 1_000_000 ≤ m) :
  ((PhiGE (m*m + 0*m + m) (m+1) : ℝ) - (PhiGE (m*m + 0*m) (m+1) : ℝ))
    ≥ Numeric.LB m 0 := by
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ 1_000_000) hm
  -- Buchstab local (x=0)
  have hCore :=
    RoughBlocks.Heavy.Buchstab.SieveX0.local_window_x0_lower_bound (m := m) hm2
  -- log(m^2)/log m = 2
  have hArg :
      Real.log ((m*m + 0*m : ℕ) : ℝ) / Real.log (m : ℝ) = (2 : ℝ) := by
    have hm_pos : 0 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (0:ℕ) < 2) hm2)
    have hlog_pos : 0 < Real.log (m : ℝ) :=
      RoughBlocks.Heavy.Numeric.log_pos_of_ge_two hm2
    have hlog_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlog_pos
    calc
      Real.log ((m*m + 0*m : ℕ) : ℝ) / Real.log (m : ℝ)
          = Real.log ((m : ℝ)^2) / Real.log (m : ℝ) := by
              simp [pow_two, Nat.cast_mul]
      _ = ((2 : ℝ) * Real.log (m : ℝ)) / Real.log (m : ℝ) := by
              simpa using Real.log_pow hm_pos 2
      _ = (2 : ℝ) := by field_simp [hlog_ne]
  -- ω(2) = 1/2
  have hω2 :
      RoughBlocks.Heavy.Buchstab.omega (2 : ℝ) = (1 : ℝ) / 2 := by
    have h1 : (1 : ℝ) ≤ 2 := by norm_num
    have h2 : (2 : ℝ) ≤ 2 := le_rfl
    simpa using RoughBlocks.Heavy.Buchstab.omega_eq_one_div (u := 2) h1 h2
  -- reconhece `Numeric.LB m 0`
  simpa [Numeric.LB, Numeric.C1Default, Numeric.C2Default,
         hArg, hω2, Nat.zero_mul, pow_two, div_eq_mul_inv,
         mul_comm, mul_left_comm, mul_assoc,
         Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
    using hCore
