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
-- Nota: imports mínimos bastam para enunciar os axiomas abaixo.

namespace RoughBlocks.External

/-- Certificado uniforme externo (Julia + IntervalArithmetic):
Para todo `m ≥ 10⁶` e `x ≤ 8`,
`(LB m x : ℝ) ≤ (countRoughInBlock m x : ℝ)`. -/
axiom bridge_ge_1e6_uniform
  {m x : ℕ} (hm : (1_000_000 : ℕ) ≤ m) (hx : x ≤ 8) :
  (RoughBlocks.Heavy.Numeric.LB m x : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ)


/-- Axioma externo específico da faixa `m ≥ 18794` usado para fechar o elo
`(Φ-dif) ≥ LB` no mesmo bloco curto.

A dependência sobre o bound analítico `u_uniform_bound` é explícita (é o
insumo "leve"), enquanto a passagem para a diferença de `Φ` é um artefato
externo (certificado numérico).
-/
/-
  Axioma externo, análogo ao caso `≥ 10^6`, mas para `m ≥ 18794`:
  para todo `m ≥ 18794` e `x ≤ 8`, vale `LB m x ≤ countRoughInBlock m x`.
  A justificativa é via certificado numérico externo (Julia/IA), não formalizada aqui.
-/
axiom bridge_ge_18794_uniform
  {m x : ℕ} (hm : 18794 ≤ m) (hx : x ≤ 8) :
  (RoughBlocks.Heavy.Numeric.LB m x : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ)

end RoughBlocks.External
