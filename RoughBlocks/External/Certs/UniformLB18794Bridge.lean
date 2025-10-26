import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.Log10Bounds
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.Heavy.Buchstab.Core
import RoughBlocks.External.Certs.UniformLB18794

namespace RoughBlocks.External.Certs.UniformLB18794Bridge
noncomputable section

open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs.UniformGE18794Bridge

/-- alvo do projeto -/
def m0 : ℕ := 18794

/-- `rows18794` tem 9 linhas (x = 0..8). -/
private lemma rows18794_length : rows18794.length = 9 := by
  native_decide

/-- índice de `rows18794` a partir de `Fin 9`. -/
private def idx (x : Fin 9) : Fin rows18794.length :=
  ⟨x, by rw [rows18794_length]; exact x.2⟩

/-- lê `finalLowerLo` direto do certificado. -/
def finalLowerLo_of (x : Fin 9) : ℚ :=
  (rows18794.get (idx x)).finalLowerLo

/-- C1 (do paper) como racional: 4.4 = 44/10. -/
def C1_q : ℚ := (44 : ℚ) / 10

/-- lower bound conservador e uniforme para ω(u).
    (0.49 é < a todos os ω_lo dos 9 blocos do JSON, então é seguro.) -/
def omegaLo_q (_x : Fin 9) : ℚ := 49 / 100

/-- vértice da parábola simplificada `f(L) = ω_lo · (L - v)^2 + const`, em ℝ. -/
def vL (x : Fin 9) : ℝ :=
  ((omegaLo_q x : ℝ) + (C1_q : ℝ)) / (2 * (omegaLo_q x : ℝ))

/-- bound numérico: com ω_lo = 0.49 e C1 = 4.4, vL < 5. -/
lemma vL_lt_five (x : Fin 9) : vL x < 5 := by
  -- vL = (0.49 + 4.4)/(2*0.49) = 4.89/0.98 ≈ 4.98979…
  have : vL x = ((49/100 : ℝ) + (44/10 : ℝ)) / (2 * (49/100 : ℝ)) := by
    simp [vL, omegaLo_q, C1_q]
  norm_num [vL, omegaLo_q, C1_q]

/-- utilidade: ω_lo > 0. -/
lemma omegaLo_pos (x : Fin 9) : 0 < (omegaLo_q x : ℝ) := by
  norm_num [omegaLo_q]

/-- diferença Φ no bloco x, no nível m. -/
@[inline] def PhiDiffAt (m : ℕ) (x : ℕ) : ℝ :=
  (PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ)

  #print axioms RoughBlocks.External.Certs.UniformLB18794Bridge.PhiDiffAt
  #check RoughBlocks.External.Certs.UniformLB18794Bridge.PhiDiffAt

/-- atalho só pra enxugar a notação do Φ-dif no alvo `m0`. -/
@[inline] def PhiDiff (x : ℕ) : ℝ :=
  ((PhiGE (m0*m0 + x*m0 + m0) (m0+1) : ℝ)
   - (PhiGE (m0*m0 + x*m0)       (m0+1) : ℝ))

/-! ### UniformLB ≤ 2 (pelo certificado) e transferência para `ℝ` -/

/-- `uniformLB ≤ 2` em ℚ, computacional (9 casos). -/
lemma uniformLB18794_le_two_q (x : Fin 9) :
    RoughBlocks.External.Certs.uniformLB18794_finalLowerLo x ≤ (2 : ℚ) := by
  -- os valores são racionais explícitos ⇒ decisão por kernel
  fin_cases x <;> native_decide

/-- versão em ℝ de `uniformLB ≤ 2`. -/
lemma uniformLB18794_le_two (x : Fin 9) :
    (RoughBlocks.External.Certs.uniformLB18794_finalLowerLo x : ℝ) ≤ (2 : ℝ) := by
  exact_mod_cast uniformLB18794_le_two_q x

/-! ### Bridge: se `Φ`-dif ≥ 2, então `Φ`-dif ≥ uniformLB (por bloco) -/

/-- se você já tem `Φ`-dif ≥ 2 para um dado bloco, então `Φ`-dif ≥ uniformLB. -/
theorem phiDiff_ge_uniformLB_18794_of_ge_two (x : Fin 9)
  (hx2 : PhiDiff (x : ℕ) ≥ (2 : ℝ)) :
  PhiDiff (x : ℕ) ≥ (RoughBlocks.External.Certs.uniformLB18794_finalLowerLo x : ℝ) := by
  exact le_trans (uniformLB18794_le_two x) hx2

/-- versão “embalada”: a partir de um pacote `ge2_all` (um por bloco),
    produzimos `Φ`-dif ≥ uniformLB uniformemente em `x : Fin 9`. -/
theorem phiDiff_ge_uniformLB_18794_all
  (ge2_all : ∀ x : Fin 9, PhiDiff (x : ℕ) ≥ (2 : ℝ)) :
  ∀ x : Fin 9, PhiDiff (x : ℕ) ≥ (RoughBlocks.External.Certs.uniformLB18794_finalLowerLo x : ℝ) :=
fun x => phiDiff_ge_uniformLB_18794_of_ge_two x (ge2_all x)

/-- versão indexada por ℕ com `x ≤ 8`. -/
theorem phiDiff_ge_uniformLB_18794_all_nat_x
  (ge2_all : ∀ x : Fin 9, PhiDiff (x : ℕ) ≥ (2 : ℝ))
  (x : ℕ) (hx : x ≤ 8) :
  PhiDiff x ≥ (RoughBlocks.External.Certs.uniformLB18794_finalLowerLoOf x hx : ℝ) := by
  simpa [RoughBlocks.External.Certs.uniformLB18794_finalLowerLoOf] using
    (phiDiff_ge_uniformLB_18794_all ge2_all ⟨x, Nat.lt_succ_of_le hx⟩)

end
end RoughBlocks.External.Certs.UniformLB18794Bridge
