import Mathlib
import RoughBlocks.External.Certs.VerifyIncrement18793
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Bridge
-- Sem axiomas: usamos apenas a ponte modular e o certificado
-- para supor a desigualdade analítica `Φ-dif ≥ LB`.

open RoughBlocks
open RoughBlocks.Heavy
open RoughBlocks.External.Certs

noncomputable section

/-- Ponte leve para `m ≥ 18793`, sem axiomas.

Premissa chave esperada do certificado embutido: a desigualdade analítica
`((PhiGE (X+Y) (m+1) : ℝ) - (PhiGE X (m+1) : ℝ)) ≥ Numeric.LB m x`,
onde `X = m^2 + x m` e `Y = m`.

Com essa premissa e a identidade de janela para o bloco curto, obtemos
`(Numeric.LB m x : ℝ) ≤ (countRoughInBlock m x : ℝ)` sem recorrer a axiomas. -/
theorem bridge_ge_18793_uniform_of_verified
  (_ : verifyIncrement18793 = true)
  {m x : ℕ} (hm : 18793 ≤ m) (hx : x ≤ 8)
  (hPhiDiff_ge_LB :
    ((PhiGE (m*m + x*m + m) (m+1) : ℝ)
      - (PhiGE (m*m + x*m) (m+1) : ℝ))
      ≥ Numeric.LB m x)
  : (Numeric.LB m x : ℝ) ≤ (countRoughInBlock m x : ℝ) := by
  -- `18793 ≤ m` ⇒ `2 ≤ m`
  have hm2 : 2 ≤ m := le_trans (by decide : (2 : ℕ) ≤ 18793) hm
  -- Igualdade bloco curto ↔ diferença de Φ (p := m+1)
  have hCountEq := countRoughInBlock_eq_phiDiff_succ_real m x hm2 hx
  -- Ponte modular
  exact LB_le_count_block (fun N _ => (PhiGE N (m+1) : ℝ)) m x hm2 hx
    (by simpa [ge_iff_le] using hPhiDiff_ge_LB)
    hCountEq
