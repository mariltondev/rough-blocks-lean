/-
BridgeFromCert18794.lean
Ponte sem admits: recibo computacional → hooks semânticos → Φ-dif ≥ LB → LB ≤ count.
-/

import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Bridge

-- dados do certificado
import RoughBlocks.External.Certs.UniformGE18794Bridge
-- verificador completo (recibo)
import RoughBlocks.External.Certs.FullVerifier
-- hooks semânticos (axiomas)
import RoughBlocks.External.Certs.BridgeSemantics18794
-- sanidade do certificado
import RoughBlocks.External.Certs.VerifyIncrement18794

import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformLB18794Bridge

namespace RoughBlocks.External


open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs
open RoughBlocks.External.Certs.FullVerifier
open RoughBlocks.External.Certs.UniformGE18794Bridge

/-- util: caracterização de `a && b = true` para `Bool`. -/
private lemma bool_and_eq_true {a b : Bool} :
  (a && b = true) ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> decide

/-- Do recibo computacional e dos hooks semânticos,
obtemos `Φ_GE(…)-Φ_GE(…) ≥ LB m x` para `m ≥ 18794`, `x ≤ 8`. -/
theorem phiDiff_ge_LB_from_cert_18794
  (hcert_full : RoughBlocks.External.Certs.FullVerifier.verify_full_certificate = true)
  {m x : ℕ} (hm : 18794 ≤ m) (hx : x ≤ 8) :
  ((PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ))
    ≥ Numeric.LB m x := by
  -- extrai a sanidade `verifyIncrement18794 = true` do recibo
  have hall_true :
      verifyIncrement18794 && (rows18794.all verify_row_calculations) = true := by
    simpa [verify_full_certificate] using hcert_full
  have ⟨hSanity, _⟩ := (bool_and_eq_true).mp hall_true

  -- hook 1: φ-dif ≥ finalLowerLo (linha x)  [precisa da sanidade]
  have hPhi_ge_final :=
    RoughBlocks.External.Certs.phiDiff_ge_row_finalLowerLo_18794
      hSanity (m := m) (x := x) hm hx
  -- hook 2: LB ≤ finalLowerLo (linha x)
  have hLB_le_final :=
    RoughBlocks.External.Certs.LB_le_row_finalLowerLo_18794
      (m := m) (x := x) hm hx

  -- encadeia: LB ≤ final ≤ φ-dif
  exact le_trans hLB_le_final hPhi_ge_final

/-- Ponte final: de `Φ-dif ≥ LB` e da identidade de janela,
obtemos `LB ≤ countRoughInBlock` para `m ≥ 18794`, `x ≤ 8`. -/
theorem bridge_ge_18794_from_verified_certificate
  (hcert_full : RoughBlocks.External.Certs.FullVerifier.verify_full_certificate = true)
  {m x : ℕ} (hm : 18794 ≤ m) (hx : x ≤ 8) :
  (Numeric.LB m x : ℝ) ≤ (countRoughInBlock m x : ℝ) := by
  -- `18794 ≤ m` ⇒ `2 ≤ m`
  have hm2 : 2 ≤ m := le_trans (by decide : (2 : ℕ) ≤ 18794) hm
  -- identidade: contagem do bloco curto = diferença de Φ_GE, p := m+1
  have hCountEq := countRoughInBlock_eq_phiDiff_succ_real m x hm2 hx
  -- bound analítico via recibo + hooks
  have hPhi := phiDiff_ge_LB_from_cert_18794 hcert_full hm hx
  -- ponte modular
  exact LB_le_count_block (fun N _ => (PhiGE N (m+1) : ℝ)) m x hm2 hx hPhi hCountEq

end RoughBlocks.External
