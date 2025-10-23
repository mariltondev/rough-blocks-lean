import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Buchstab.Core
import RoughBlocks.External.Certs.UniformGE18794Bridge

namespace RoughBlocks.External.Certs

open RoughBlocks RoughBlocks.Heavy

/-- Fixamos m = 18794 e x = 0. -/
def m0 : ℕ := 18794
def x0 : ℕ := 0

/-- Testemunhas (duas primas no bloco curto (m^2, m^2+m]). -/
def n₁ : ℕ := 353214437
def n₂ : ℕ := 353214443

/-- Primalidade. -/
lemma prime_n₁ : Nat.Prime n₁ := by native_decide
lemma prime_n₂ : Nat.Prime n₂ := by native_decide

/-- n₁ está no bloco curto K m0 0 = [m0^2+1, m0^2+m0]. -/
lemma n₁_in_block : n₁ ∈ K m0 x0 := by
  have hL : m0^2 + 1 ≤ n₁ := by native_decide
  have hR : n₁ ≤ m0^2 + m0 := by native_decide
  simp [K, x0]
  exact ⟨hL, hR⟩

/-- n₂ está no bloco curto K m0 0. -/
lemma n₂_in_block : n₂ ∈ K m0 x0 := by
  have hL : m0^2 + 1 ≤ n₂ := by native_decide
  have hR : n₂ ≤ m0^2 + m0 := by native_decide
  simp [K, x0]
  exact ⟨hL, hR⟩

/-- Lema utilitário: primo ≥ m+1 ⇒ m-áspero. -/
lemma prime_ge_succ_m_implies_mRough {m n : ℕ} (hn : Nat.Prime n) (h : m + 1 ≤ n) :
    mRough m n := by
  intro p hp hdiv
  have hcases := (Nat.dvd_prime hn).1 hdiv
  rcases hcases with (h1 | h2)
  · exact (hp.ne_one h1).elim
  · have : p = n := h2
    rw [this]
    exact h

/-- n₁ é m-áspero (m=m0). -/
lemma n₁_is_rough : mRough m0 n₁ := by
  have hm : m0 + 1 ≤ n₁ := by native_decide
  exact prime_ge_succ_m_implies_mRough prime_n₁ hm

/-- n₂ é m-áspero (m=m0). -/
lemma n₂_is_rough : mRough m0 n₂ := by
  have hm : m0 + 1 ≤ n₂ := by native_decide
  exact prime_ge_succ_m_implies_mRough prime_n₂ hm

/-- Com duas testemunhas distintas, a contagem é ≥ 2. -/
lemma count_ge_two_from_two_witnesses : 2 ≤ countRoughInBlock m0 x0 := by
  classical
  have h₁S : n₁ ∈ (K m0 x0).filter (mRough m0) := by
    simp [Finset.mem_filter, n₁_in_block, n₁_is_rough]
  have h₂S : n₂ ∈ (K m0 x0).filter (mRough m0) := by
    simp [Finset.mem_filter, n₂_in_block, n₂_is_rough]
  have hneq : n₁ ≠ n₂ := by native_decide
  have hlt : 1 < ((K m0 x0).filter (mRough m0)).card :=
    Finset.one_lt_card.mpr ⟨n₁, h₁S, n₂, h₂S, hneq⟩
  have : 2 ≤ ((K m0 x0).filter (mRough m0)).card := Nat.succ_le_of_lt hlt
  simpa [countRoughInBlock]

/-- Φ-diferença ≥ 2 -/
lemma phiDiff_ge_two :
    ((PhiGE (m0^2 + m0) (m0 + 1) : ℝ) - (PhiGE (m0^2) (m0 + 1) : ℝ)) ≥ (2 : ℝ) := by
  have hm2 : 2 ≤ m0 := by native_decide
  have hx : x0 ≤ 8 := by native_decide
  have hCountEq := countRoughInBlock_eq_phiDiff_succ_real m0 x0 hm2 hx
  have hCount_ge₂_nat : 2 ≤ countRoughInBlock m0 x0 := count_ge_two_from_two_witnesses
  have hCount_ge₂_real : (2 : ℝ) ≤ (countRoughInBlock m0 x0 : ℝ) := by exact_mod_cast hCount_ge₂_nat
  rw [hCountEq] at hCount_ge₂_real
  exact hCount_ge₂_real

/-! ### Agora: pegar o `finalLowerLo` **direto** do certificado -/

/-- O certificado tem 9 linhas (x = 0..8). -/
private lemma rows18794_length : rows18794.length = 9 := by native_decide

/-- Índice finito para a linha x=0 do certificado. -/
private def ix0 : Fin rows18794.length :=
  ⟨0, by
    -- objetivo: 0 < rows18794.length
    -- reescreve para `0 < 9` e fecha por decisão
    rw [rows18794_length]
    decide⟩

/-- `finalLowerLo` da linha x=0, lido diretamente de `rows18794`. -/
def certified_finalLowerLo_x0 : ℚ :=
  (rows18794.get ix0).finalLowerLo

/-- Bound racional: `finalLowerLo ≤ 2`. -/
lemma certified_value_le_two_q : certified_finalLowerLo_x0 ≤ (2 : ℚ) := by
  -- o kernel avalia `get` e compara racionais exatos
  native_decide

/-- Versão em ℝ. -/
lemma certified_value_le_two : (certified_finalLowerLo_x0 : ℝ) ≤ (2 : ℝ) := by
  exact_mod_cast certified_value_le_two_q

/-- Teorema final sem axiomas (x = 0). -/
theorem phiDiff_ge_row_finalLowerLo_18794_case0_no_axioms :
    ((PhiGE (m0^2 + m0) (m0 + 1) : ℝ) - (PhiGE (m0^2) (m0 + 1) : ℝ)) ≥
    (certified_finalLowerLo_x0 : ℝ) := by
  have hφ_ge_two :
      ((PhiGE (m0^2 + m0) (m0 + 1) : ℝ) - (PhiGE (m0^2) (m0 + 1) : ℝ)) ≥ (2 : ℝ) :=
    phiDiff_ge_two
  linarith [hφ_ge_two, certified_value_le_two]

#print axioms RoughBlocks.External.Certs.phiDiff_ge_row_finalLowerLo_18794_case0_no_axioms
#print axioms RoughBlocks.External.Certs.phiDiff_ge_two
#print axioms RoughBlocks.External.Certs.count_ge_two_from_two_witnesses

end RoughBlocks.External.Certs
