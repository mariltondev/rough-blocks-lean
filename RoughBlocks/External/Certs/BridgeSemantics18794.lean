/-
SPDX-License-Identifier: Apache-2.0

Camada mínima de semântica para os `BridgeRow`s do certificado ≥ 18794.

Fornece dois axiomas localizados que formalizam o significado dos campos
da linha selecionada para `x ∈ {0,…,8}`:
  1) a diferença telescópica de `PhiGE` (com `p := m+1`) é
     majorante inferior por `finalLowerLo` daquela linha;
  2) o lado analítico `Numeric.LB m x` é no máximo esse mesmo
     `finalLowerLo`.

Esses axiomas isolam a dependência do certificado numérico externo, de modo
que o restante do elo (ponte bloco ↔ janela e aritmética real-elementar)
permaneça livre de axiomas.
-/

import Mathlib
import RoughBlocks.Heavy.Buchstab.Core   -- PhiGE
import RoughBlocks.Heavy.Numeric         -- LB
import RoughBlocks.External.Certs.VerifyIncrement18794
import RoughBlocks.External.Certs.UniformGE18794Bridge
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace RoughBlocks.External.Certs

open RoughBlocks RoughBlocks.Heavy

/-- Seleciona a linha `rows18794` correspondente a `x ≤ 8`. -/
def row18794Of (x : ℕ) (hx : x ≤ 8) : BridgeRow :=
  -- provamos `x < length rows18794 = 9` e usamos `List.get` diretamente
  have hlen : rows18794.length = 9 := by
    -- `rows18794` é um literal com 9 entradas
    simp [rows18794]
  have hxlt : x < rows18794.length := by
    simpa [hlen] using Nat.lt_of_le_of_lt hx (by decide : 8 < 9)
  rows18794.get ⟨x, hxlt⟩

/-- Axioma (semântica do certificado): na janela curta com `p := m+1`,
`PhiGE(X+Y,p) - PhiGE(X,p) ≥ finalLowerLo` da linha `x`.

Pré-condições: o verificador estrutural passou; `m ≥ 18794`, `x ≤ 8`.
-/
axiom phiDiff_ge_row_finalLowerLo_18794
  (hcert : verifyIncrement18794 = true)
  {m x : ℕ} (hm : 18794 ≤ m) (hx : x ≤ 8) :
  let r := row18794Of x hx
  ((PhiGE (m*m + x*m + m) (m+1) : ℝ)
    - (PhiGE (m*m + x*m) (m+1) : ℝ)) ≥ (r.finalLowerLo : ℝ)

/-- Axioma (ligação `LB` → linha): o `LB m x` analítico é no máximo o
`finalLowerLo` da linha `x` do certificado para `m ≥ 18794`.
-/
axiom LB_le_row_finalLowerLo_18794
  {m x : ℕ} (hm : 18794 ≤ m) (hx : x ≤ 8) :
  let r := row18794Of x hx
  (Numeric.LB m x : ℝ) ≤ (r.finalLowerLo : ℝ)


end RoughBlocks.External.Certs
