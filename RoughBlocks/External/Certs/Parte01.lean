import Mathlib
import RoughBlocks.Heavy.Interface
import RoughBlocks.External.Certs.UniformLB18794Bridge

namespace RoughBlocks.External.Certs

open RoughBlocks.Heavy
open RoughBlocks.External.Certs.UniformLB18794Bridge

/-
Parte 1: fatos estáticos computacionais e a tabela uniformLB > 1.
Tudo via `decide`/`native_decide` (sem `admit`).
-/

/-- Fato estático: `U0Default ≤ BridgeThreshold`. -/
lemma U0Default_le_BridgeThreshold : (U0Default : ℕ) ≤ (BridgeThreshold : ℕ) := by
  decide

/-- Fato estático: `BridgeThreshold ≤ m0`. -/
lemma BridgeThreshold_le_m0 : (BridgeThreshold : ℕ) ≤ (m0 : ℕ) := by
  decide

/-- Corolário útil: `U0Default ≤ m0`. -/
lemma U0Default_le_m0 : (U0Default : ℕ) ≤ (m0 : ℕ) :=
  le_trans U0Default_le_BridgeThreshold BridgeThreshold_le_m0

/-- “Lift” conveniente: de `m0 ≤ m` obtemos `U0Default ≤ m`. -/
lemma U0Default_le_m_of_ge_m0 {m : ℕ} (hm : (m0 : ℕ) ≤ m) :
    (U0Default : ℕ) ≤ m :=
  le_trans U0Default_le_m0 hm

/-- Fato estático: `2 ≤ m0`. -/
lemma two_le_m0 : (2 : ℕ) ≤ (m0 : ℕ) := by
  decide

/-- “Lift” conveniente: de `m0 ≤ m` obtemos `2 ≤ m`. -/
lemma two_le_m_of_ge_m0 {m : ℕ} (hm : (m0 : ℕ) ≤ m) : (2 : ℕ) ≤ m :=
  le_trans two_le_m0 hm

/-- Fato estático: `10000 ≤ m0`. -/
lemma tenThousand_le_m0 : (10000 : ℕ) ≤ (m0 : ℕ) := by
  decide

/-- Tabela computacional (versão racional): `uniformLB18794_finalLowerLo x > 1`. -/
lemma uniformLB18794_gt_one_q (x : Fin 9) :
  uniformLB18794_finalLowerLo x > (1 : ℚ) := by
  -- varre os 9 casos por decisão nativa
  fin_cases x <;> native_decide

/-- Tabela computacional (versão real): `uniformLB18794_finalLowerLo x > 1`. -/
lemma uniformLB18794_gt_one (x : Fin 9) :
  (uniformLB18794_finalLowerLo x : ℝ) > (1 : ℝ) := by
  exact_mod_cast (uniformLB18794_gt_one_q x)

end RoughBlocks.External.Certs
