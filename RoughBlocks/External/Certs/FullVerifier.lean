import Mathlib
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.VerifyIncrement18794 -- Onde está rows18794 e a verificação de sanidade

namespace RoughBlocks.External.Certs.FullVerifier

open RoughBlocks.External.Certs
open RoughBlocks.External.Certs.UniformGE18794Bridge

/-!
### Auditoria de Cálculo

Verificamos se as desigualdades-chave do paper são satisfeitas pelos
números exatos (ℚ) do certificado.
-/

-- Implementação da fórmula do seu paper que calcula o limite inferior final.
-- Esta função deve corresponder exatamente à sua teoria.
-- Exemplo hipotético:
def calculate_final_lower_bound (row : BridgeRow) : ℚ :=
  row.tMainLo - row.m2Lo - row.rLo - row.e1Up - row.e2

-- Para cada linha, verificamos se o limite inferior recalculado
-- é de fato maior ou igual ao limite inferior que o certificado afirma.
def verify_row_calculations (row : BridgeRow) : Bool :=
  let recalculated_lb := calculate_final_lower_bound row
  -- A verificação crucial!
  decide (recalculated_lb ≥ row.finalLowerLo)

-- A verificação completa: sanidade E cálculos.
def verify_full_certificate : Bool :=
  -- Primeiro, rodamos as checagens de sanidade que você já criou.
  verifyIncrement18794 &&
  -- Se passaram, verificamos os cálculos de todas as linhas.
  (rows18794.all verify_row_calculations)

-- Agora, provamos que nosso certificado PASSA nesta verificação completa.
-- Este é o pilar da nossa ponte no lado computacional.
theorem full_certificate_is_valid : verify_full_certificate = true := by
  native_decide -- Roda o auditor em todos os dados e confirma que o resultado é `true`.

end RoughBlocks.External.Certs.FullVerifier
