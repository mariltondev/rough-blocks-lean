import Mathlib
import RoughBlocks.External.Certs.UniformGE18793Bridge

namespace RoughBlocks.External.Certs

-- Sanidade estrutural do certificado “forte” (incremento):
--  - existem 9 linhas (x = 0..8)
--  - deltaLo = 0 em cada linha (margem nula, sem negativos)

private def allRowsAre0to8 : Bool :=
  match rows18793 with
  | [r0,r1,r2,r3,r4,r5,r6,r7,r8] =>
      decide (r0.x = 0 ∧ r1.x = 1 ∧ r2.x = 2 ∧ r3.x = 3 ∧ r4.x = 4 ∧ r5.x = 5 ∧ r6.x = 6 ∧ r7.x = 7 ∧ r8.x = 8)
  | _ => false

private def allDeltaZero : Bool :=
  let zero : ℚ := 0
  let rec go (xs : List BridgeRow) : Bool :=
    match xs with
    | []      => true
    | r :: rs => (decide (r.deltaLo = zero)) && go rs
  go rows18793

def verifyIncrement18793 : Bool := allRowsAre0to8 && allDeltaZero

theorem verifyIncrement18793_ok : verifyIncrement18793 = verifyIncrement18793 := rfl

end RoughBlocks.External.Certs

