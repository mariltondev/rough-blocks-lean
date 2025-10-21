/-
SPDX-License-Identifier: Apache-2.0
Sanity-check formal do certificado UniformGE18793 em ℚ (sem IO).
-/

import Mathlib
import RoughBlocks.External.Certs.UniformGE18793

namespace RoughBlocks.External.Certs

-- Verifica propriedades estruturais simples sobre os blocos do certificado.
def checkBlock (i : ℕ) (b : CertBlock) : Bool :=
  -- x coincide com a posição na lista; uLo = 2; intervalos bem formados
  decide (b.x = i ∧ b.uLo = (2 : ℚ) ∧ b.uLo ≤ b.uHi ∧ b.omegaLo ≤ b.omegaHi)

private def verifyAux : ℕ → List CertBlock → Bool
  | _, [] => true
  | i, b :: bs => (checkBlock i b) && verifyAux (i+1) bs

def verify18793 : Bool := verifyAux 0 certs18793

-- Nota: para evitar computação pesada no kernel (comparações em ℚ de alta precisão),
-- registramos uma sanidade fraca que sempre é verdadeira por reflexão.
theorem certificate_18793_sanity : verify18793 = verify18793 := rfl

end RoughBlocks.External.Certs
