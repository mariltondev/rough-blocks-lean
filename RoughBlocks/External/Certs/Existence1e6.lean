import Mathlib
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.External.Certs.UniformGE1e6Bridge

noncomputable section
namespace RoughBlocks.External.Certs
open Classical Real
open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs.UniformGE1e6Bridge
--import RoughBlocks.External.Certs.Row0_Soundness

/-- Limiar global do certificado atual (1e6). -/
def m₀ : ℕ := 1_000_000

/-- Atalho: Φ-dif na janela curta (def da camada Heavy). -/
abbrev PhiDiffAt (m x : ℕ) : ℝ := RoughBlocks.Heavy.PhiDiffAt m x

/-- Valor racional do "finalLowerLo" da linha 0 do certificado. -/
def q0 : ℚ := (row0.finalLowerLo : ℚ)

/-- Certificado por-linha (Row 0):
  1) `finalLowerLo` realmente coincide com `q0` (em ℚ);
  2) para todo `m ≥ m₀`, a contagem no bloco 0 é ≥ `q0` (em ℝ). -/
structure Row0Certificate : Prop where
  finalLo_is_q : (row0.finalLowerLo : ℚ) = q0
  count_ge_q   : ∀ {m : ℕ}, m₀ ≤ m → (countRoughInBlock m 0 : ℝ) ≥ (q0 : ℝ)

/-- **Teorema (Row 0, m ≥ 1e6, sem axioma):**
    Do certificado acima, conclui-se `Φ-dif(m,0) ≥ finalLowerLo(row0)` para todo `m ≥ m₀`. -/
theorem phiDiff_ge_row0_finalLowerLo_1e6_of_certificate
  (hc : Row0Certificate) {m : ℕ} (hm : m₀ ≤ m) :
  PhiDiffAt m 0 ≥ (row0.finalLowerLo : ℝ) := by
  -- janela curta: `count = Φ`
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ m₀) hm
  have hx  : (0 : ℕ) ≤ 8 := by decide
  have hEq : (countRoughInBlock m 0 : ℝ) = PhiDiffAt m 0 := by
    simpa [PhiDiffAt, RoughBlocks.Heavy.PhiDiffAt, Nat.zero_mul, zero_mul] using
      (countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := 0) hm2 hx)
  -- `finalLowerLo = q0` em ℚ ⇒ coerção para ℝ
  have hFL : (row0.finalLowerLo : ℝ) = (q0 : ℝ) := by
    simpa using congrArg (fun r : ℚ => (r : ℝ)) hc.finalLo_is_q
  -- usa o bound do certificado na contagem e reescreve por Φ
  calc
    PhiDiffAt m 0
        = (countRoughInBlock m 0 : ℝ) := hEq.symm
    _   ≥ (q0 : ℝ)                    := hc.count_ge_q hm
    _   = (row0.finalLowerLo : ℝ)     := hFL.symm

/-- **Corolário (Row 0):** para todo `m ≥ 1e6`, `Φ-dif(m,0) ≥ 1`. -/
theorem phiDiff_row0_ge_one_1e6
  (hc : Row0Certificate) {m : ℕ} (hm : m₀ ≤ m) :
  PhiDiffAt m 0 ≥ (1 : ℝ) := by
  -- Reescreve ambos em forma `≤` para usar `le_trans`.
  have h1 : (row0.finalLowerLo : ℝ) ≤ PhiDiffAt m 0 := by
    simpa [ge_iff_le] using (phiDiff_ge_row0_finalLowerLo_1e6_of_certificate hc hm)
  have h2 : (1 : ℝ) ≤ (row0.finalLowerLo : ℝ) := by
    simpa [ge_iff_le] using row0_finalLowerLo_ge_one_real
  have : (1 : ℝ) ≤ PhiDiffAt m 0 := le_trans h2 h1
  simpa [ge_iff_le] using this

/-- **Versão em `count`:** `count ≥ 1` (existe um m-áspero no bloco 0). -/
theorem count_row0_ge_one_1e6
  (hc : Row0Certificate) {m : ℕ} (hm : m₀ ≤ m) :
  (countRoughInBlock m 0 : ℝ) ≥ (1 : ℝ) := by
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ m₀) hm
  have hx  : (0 : ℕ) ≤ 8 := by decide
  have hEq : (countRoughInBlock m 0 : ℝ) = PhiDiffAt m 0 := by
    simpa [PhiDiffAt, RoughBlocks.Heavy.PhiDiffAt, Nat.zero_mul, zero_mul] using
      (countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := 0) hm2 hx)
  have hφ : PhiDiffAt m 0 ≥ (1 : ℝ) := phiDiff_row0_ge_one_1e6 hc hm
  simpa [hEq, ge_iff_le] using hφ

/-- Certificado por-linha **materializado** a partir do bound numérico do bridge. -/
def Row0Certificate_from_pipeline : Row0Certificate :=
{ finalLo_is_q := rfl,
  count_ge_q := by
    intro m hm
    -- converte `m₀ ≤ m` em `1000000 ≤ m` para usar o lema do bridge:
    have hm' : 1000000 ≤ m := by simpa [m₀] using hm
    -- usa o bound numérico do `UniformGE1e6Bridge` e reescreve `q0`:
    simpa [q0] using
      RoughBlocks.External.Certs.UniformGE1e6Bridge.row0_count_ge_finalLowerLo_1e6
        (m := m) hm' }




/-- Versão sem fornecer o certificado manualmente: usa o derivado da pipeline. -/
theorem count_row0_ge_one_1e6_noHyp {m : ℕ} (hm : m₀ ≤ m) :
  (countRoughInBlock m 0 : ℝ) ≥ (1 : ℝ) :=
  count_row0_ge_one_1e6 Row0Certificate_from_pipeline hm

theorem phiDiff_row0_ge_one_1e6_noHyp {m : ℕ} (hm : m₀ ≤ m) :
  PhiDiffAt m 0 ≥ (1 : ℝ) :=
  phiDiff_row0_ge_one_1e6 Row0Certificate_from_pipeline hm


#print axioms RoughBlocks.External.Certs.phiDiff_row0_ge_one_1e6_noHyp
#check RoughBlocks.External.Certs.phiDiff_row0_ge_one_1e6_noHyp
#print m₀

end RoughBlocks.External.Certs
