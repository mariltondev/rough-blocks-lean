/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric

namespace RoughBlocks.External

/-- Certificado uniforme externo (Julia + IntervalArithmetic):
Para todo `m ≥ 10⁶` e `x ≤ 8`,
`(LB m x : ℝ) ≤ (countRoughInBlock m x : ℝ)`. -/
axiom bridge_ge_1e6_uniform
  {m x : ℕ} (hm : (1_000_000 : ℕ) ≤ m) (hx : x ≤ 8) :
  (RoughBlocks.Heavy.Numeric.LB m x : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ)

end RoughBlocks.External
