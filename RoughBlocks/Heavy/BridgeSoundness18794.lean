import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Bridge
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.VerifyIncrement18794
import RoughBlocks.External.Certs.FullVerifier
import RoughBlocks.External.BridgeFromCert18794

open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs.FullVerifier

noncomputable section

theorem bridge_ge_18794_uniform_fully_verified
  {m x : ℕ} (hm : 18794 ≤ m) (hx : x ≤ 8) :
  (Numeric.LB m x : ℝ) ≤ (countRoughInBlock m x : ℝ) :=
  RoughBlocks.External.bridge_ge_18794_from_verified_certificate
    full_certificate_is_valid
    hm
    hx

end
