import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Buchstab.Core
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794

namespace RoughBlocks.External.Certs

open RoughBlocks RoughBlocks.Heavy

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

/-- para todo `x : Fin 9`, `finalLowerLo ≤ 2` (ℚ) — computacional. -/
lemma finalLowerLo_of_le_two_q (x : Fin 9) :
    finalLowerLo_of x ≤ (2 : ℚ) := by
  fin_cases x <;> native_decide

/-- versão em ℝ. -/
lemma finalLowerLo_of_le_two (x : Fin 9) :
    (finalLowerLo_of x : ℝ) ≤ (2 : ℝ) := by
  exact_mod_cast finalLowerLo_of_le_two_q x

/-- primo ≥ m+1 ⇒ m-áspero. -/
lemma prime_ge_succ_m_implies_mRough
    {m n : ℕ} (hn : Nat.Prime n) (h : m + 1 ≤ n) : mRough m n := by
  intro p hp hdiv
  have hcases := (Nat.dvd_prime hn).1 hdiv
  rcases hcases with (h1 | h2)
  · exact (hp.ne_one h1).elim
  · have : p = n := h2
    rw [this]
    exact h

/-- Pacote de duas testemunhas para o bloco `x`. -/
structure WitnessPkg (x : Fin 9) where
  n1 : ℕ
  n2 : ℕ
  prime_n1 : Nat.Prime n1
  prime_n2 : Nat.Prime n2
  in_block1 : n1 ∈ K m0 (x : ℕ)
  in_block2 : n2 ∈ K m0 (x : ℕ)
  ge_succ1 : m0 + 1 ≤ n1
  ge_succ2 : m0 + 1 ≤ n2
  ne12 : n1 ≠ n2

/-- Duas testemunhas ⇒ `Φ_GE`-dif ≥ 2. -/
lemma phiDiff_ge_two_of (x : Fin 9) (W : WitnessPkg x) :
    ((PhiGE (m0 * m0 + (x : ℕ) * m0 + m0) (m0 + 1) : ℝ)
     - (PhiGE (m0 * m0 + (x : ℕ) * m0) (m0 + 1) : ℝ)) ≥ (2 : ℝ) := by
  classical
  -- m-aspereza
  have r1 : mRough m0 W.n1 := prime_ge_succ_m_implies_mRough W.prime_n1 W.ge_succ1
  have r2 : mRough m0 W.n2 := prime_ge_succ_m_implies_mRough W.prime_n2 W.ge_succ2
  -- entram no finset filtrado
  have h1S : W.n1 ∈ (K m0 (x : ℕ)).filter (mRough m0) := by
    simp [Finset.mem_filter, W.in_block1, r1]
  have h2S : W.n2 ∈ (K m0 (x : ℕ)).filter (mRough m0) := by
    simp [Finset.mem_filter, W.in_block2, r2]
  -- card ≥ 2
  have hlt : 1 < ((K m0 (x : ℕ)).filter (mRough m0)).card :=
    Finset.one_lt_card.mpr ⟨W.n1, h1S, W.n2, h2S, W.ne12⟩
  have hCount_ge₂_nat : 2 ≤ ((K m0 (x : ℕ)).filter (mRough m0)).card :=
    Nat.succ_le_of_lt hlt
  have hCount_ge₂_nat' : 2 ≤ countRoughInBlock m0 (x : ℕ) := by
    simpa [countRoughInBlock] using hCount_ge₂_nat
  -- ℕ → ℝ
  have hCount_ge₂_real : (2 : ℝ) ≤ (countRoughInBlock m0 (x : ℕ) : ℝ) := by
    exact_mod_cast hCount_ge₂_nat'
  -- identidade janela ↔ Φ
  have hm2 : 2 ≤ m0 := by decide
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  have hEq := countRoughInBlock_eq_phiDiff_succ_real (m := m0) (x := (x : ℕ)) hm2 hx
  rw [hEq] at hCount_ge₂_real
  exact hCount_ge₂_real

/-- Fechamento genérico: com duas testemunhas, `Φ-dif ≥ finalLowerLo(x)`. -/
theorem phiDiff_ge_row_finalLowerLo_18794_of (x : Fin 9) (W : WitnessPkg x) :
    ((PhiGE (m0 * m0 + (x : ℕ) * m0 + m0) (m0 + 1) : ℝ)
     - (PhiGE (m0 * m0 + (x : ℕ) * m0) (m0 + 1) : ℝ))
    ≥ (finalLowerLo_of x : ℝ) := by
  have h1 : ((PhiGE (m0 * m0 + (x : ℕ) * m0 + m0) (m0 + 1) : ℝ)
            - (PhiGE (m0 * m0 + (x : ℕ) * m0) (m0 + 1) : ℝ)) ≥ (2 : ℝ) :=
    phiDiff_ge_two_of x W
  have h2 : (finalLowerLo_of x : ℝ) ≤ (2 : ℝ) := finalLowerLo_of_le_two x
  linarith


-- ------ Bloco x = 0 -------
def x0 : Fin 9 := ⟨0, by decide⟩
def n₁_x0 : ℕ := 353214437
def n₂_x0 : ℕ := 353214443

lemma n₁_x0_in_block : n₁_x0 ∈ K m0 (x0 : ℕ) := by
  have hL : m0 ^ 2 + 1 ≤ n₁_x0 := by native_decide
  have hR : n₁_x0 ≤ m0 ^ 2 + m0 := by native_decide
  simp [K, x0]
  exact ⟨hL, hR⟩

lemma n₂_x0_in_block : n₂_x0 ∈ K m0 (x0 : ℕ) := by
  have hL : m0 ^ 2 + 1 ≤ n₂_x0 := by native_decide
  have hR : n₂_x0 ≤ m0 ^ 2 + m0 := by native_decide
  simp [K, x0]
  exact ⟨hL, hR⟩

def W0 : WitnessPkg x0 :=
  { n1 := n₁_x0
    n2 := n₂_x0
    prime_n1 := by native_decide
    prime_n2 := by native_decide
    in_block1 := n₁_x0_in_block
    in_block2 := n₂_x0_in_block
    ge_succ1 := by native_decide
    ge_succ2 := by native_decide
    ne12 := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case0_no_axioms :
    ((PhiGE (m0 * m0 + (x0 : ℕ) * m0 + m0) (m0 + 1) : ℝ)
     - (PhiGE (m0 * m0 + (x0 : ℕ) * m0) (m0 + 1) : ℝ))
    ≥ (finalLowerLo_of x0 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x0 W0


-- ------ Bloco x = 1 -------
def x1 : Fin 9 := ⟨1, by decide⟩
def n₁_x1 : ℕ := 353233277
def n₂_x1 : ℕ := 353233289

lemma n₁_x1_in_block : n₁_x1 ∈ K m0 (x1 : ℕ) := by
  have hL : m0 ^ 2 + (x1 : ℕ) * m0 + 1 ≤ n₁_x1 := by native_decide
  have hR : n₁_x1 ≤ m0 ^ 2 + (x1 : ℕ) * m0 + m0 := by native_decide
  simp [K, x1]; exact ⟨hL, hR⟩

lemma n₂_x1_in_block : n₂_x1 ∈ K m0 (x1 : ℕ) := by
  have hL : m0 ^ 2 + (x1 : ℕ) * m0 + 1 ≤ n₂_x1 := by native_decide
  have hR : n₂_x1 ≤ m0 ^ 2 + (x1 : ℕ) * m0 + m0 := by native_decide
  simp [K, x1]; exact ⟨hL, hR⟩

def W1 : WitnessPkg x1 :=
  { n1 := n₁_x1, n2 := n₂_x1
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x1_in_block
  , in_block2 := n₂_x1_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case1_no_axioms :
    ((PhiGE (m0*m0 + (x1:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x1:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x1 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x1 W1


-- ------ Bloco x = 2 -------
def x2 : Fin 9 := ⟨2, by decide⟩
def n₁_x2 : ℕ := 353252071
def n₂_x2 : ℕ := 353252077

lemma n₁_x2_in_block : n₁_x2 ∈ K m0 (x2 : ℕ) := by
  have hL : m0 ^ 2 + (x2 : ℕ) * m0 + 1 ≤ n₁_x2 := by native_decide
  have hR : n₁_x2 ≤ m0 ^ 2 + (x2 : ℕ) * m0 + m0 := by native_decide
  simp [K, x2]; exact ⟨hL, hR⟩

lemma n₂_x2_in_block : n₂_x2 ∈ K m0 (x2 : ℕ) := by
  have hL : m0 ^ 2 + (x2 : ℕ) * m0 + 1 ≤ n₂_x2 := by native_decide
  have hR : n₂_x2 ≤ m0 ^ 2 + (x2 : ℕ) * m0 + m0 := by native_decide
  simp [K, x2]; exact ⟨hL, hR⟩

def W2 : WitnessPkg x2 :=
  { n1 := n₁_x2, n2 := n₂_x2
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x2_in_block
  , in_block2 := n₂_x2_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case2_no_axioms :
    ((PhiGE (m0*m0 + (x2:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x2:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x2 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x2 W2


-- ------ Bloco x = 3 -------
def x3 : Fin 9 := ⟨3, by decide⟩
def n₁_x3 : ℕ := 353270839
def n₂_x3 : ℕ := 353270849

lemma n₁_x3_in_block : n₁_x3 ∈ K m0 (x3 : ℕ) := by
  have hL : m0 ^ 2 + (x3 : ℕ) * m0 + 1 ≤ n₁_x3 := by native_decide
  have hR : n₁_x3 ≤ m0 ^ 2 + (x3 : ℕ) * m0 + m0 := by native_decide
  simp [K, x3]; exact ⟨hL, hR⟩

lemma n₂_x3_in_block : n₂_x3 ∈ K m0 (x3 : ℕ) := by
  have hL : m0 ^ 2 + (x3 : ℕ) * m0 + 1 ≤ n₂_x3 := by native_decide
  have hR : n₂_x3 ≤ m0 ^ 2 + (x3 : ℕ) * m0 + m0 := by native_decide
  simp [K, x3]; exact ⟨hL, hR⟩

def W3 : WitnessPkg x3 :=
  { n1 := n₁_x3, n2 := n₂_x3
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x3_in_block
  , in_block2 := n₂_x3_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case3_no_axioms :
    ((PhiGE (m0*m0 + (x3:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x3:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x3 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x3 W3


-- ------ Bloco x = 4 -------
def x4 : Fin 9 := ⟨4, by decide⟩
def n₁_x4 : ℕ := 353289649
def n₂_x4 : ℕ := 353289697

lemma n₁_x4_in_block : n₁_x4 ∈ K m0 (x4 : ℕ) := by
  have hL : m0 ^ 2 + (x4 : ℕ) * m0 + 1 ≤ n₁_x4 := by native_decide
  have hR : n₁_x4 ≤ m0 ^ 2 + (x4 : ℕ) * m0 + m0 := by native_decide
  simp [K, x4]; exact ⟨hL, hR⟩

lemma n₂_x4_in_block : n₂_x4 ∈ K m0 (x4 : ℕ) := by
  have hL : m0 ^ 2 + (x4 : ℕ) * m0 + 1 ≤ n₂_x4 := by native_decide
  have hR : n₂_x4 ≤ m0 ^ 2 + (x4 : ℕ) * m0 + m0 := by native_decide
  simp [K, x4]; exact ⟨hL, hR⟩

def W4 : WitnessPkg x4 :=
  { n1 := n₁_x4, n2 := n₂_x4
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x4_in_block
  , in_block2 := n₂_x4_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case4_no_axioms :
    ((PhiGE (m0*m0 + (x4:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x4:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x4 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x4 W4


-- ------ Bloco x = 5 -------
def x5 : Fin 9 := ⟨5, by decide⟩
def n₁_x5 : ℕ := 353308409
def n₂_x5 : ℕ := 353308463

lemma n₁_x5_in_block : n₁_x5 ∈ K m0 (x5 : ℕ) := by
  have hL : m0 ^ 2 + (x5 : ℕ) * m0 + 1 ≤ n₁_x5 := by native_decide
  have hR : n₁_x5 ≤ m0 ^ 2 + (x5 : ℕ) * m0 + m0 := by native_decide
  simp [K, x5]; exact ⟨hL, hR⟩

lemma n₂_x5_in_block : n₂_x5 ∈ K m0 (x5 : ℕ) := by
  have hL : m0 ^ 2 + (x5 : ℕ) * m0 + 1 ≤ n₂_x5 := by native_decide
  have hR : n₂_x5 ≤ m0 ^ 2 + (x5 : ℕ) * m0 + m0 := by native_decide
  simp [K, x5]; exact ⟨hL, hR⟩

def W5 : WitnessPkg x5 :=
  { n1 := n₁_x5, n2 := n₂_x5
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x5_in_block
  , in_block2 := n₂_x5_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case5_no_axioms :
    ((PhiGE (m0*m0 + (x5:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x5:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x5 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x5 W5


-- ------ Bloco x = 6 -------
def x6 : Fin 9 := ⟨6, by decide⟩
def n₁_x6 : ℕ := 353327207
def n₂_x6 : ℕ := 353327237

lemma n₁_x6_in_block : n₁_x6 ∈ K m0 (x6 : ℕ) := by
  have hL : m0 ^ 2 + (x6 : ℕ) * m0 + 1 ≤ n₁_x6 := by native_decide
  have hR : n₁_x6 ≤ m0 ^ 2 + (x6 : ℕ) * m0 + m0 := by native_decide
  simp [K, x6]; exact ⟨hL, hR⟩

lemma n₂_x6_in_block : n₂_x6 ∈ K m0 (x6 : ℕ) := by
  have hL : m0 ^ 2 + (x6 : ℕ) * m0 + 1 ≤ n₂_x6 := by native_decide
  have hR : n₂_x6 ≤ m0 ^ 2 + (x6 : ℕ) * m0 + m0 := by native_decide
  simp [K, x6]; exact ⟨hL, hR⟩

def W6 : WitnessPkg x6 :=
  { n1 := n₁_x6, n2 := n₂_x6
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x6_in_block
  , in_block2 := n₂_x6_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case6_no_axioms :
    ((PhiGE (m0*m0 + (x6:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x6:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x6 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x6 W6


-- ------ Bloco x = 7 -------
def x7 : Fin 9 := ⟨7, by decide⟩
def n₁_x7 : ℕ := 353345999
def n₂_x7 : ℕ := 353346001

lemma n₁_x7_in_block : n₁_x7 ∈ K m0 (x7 : ℕ) := by
  have hL : m0 ^ 2 + (x7 : ℕ) * m0 + 1 ≤ n₁_x7 := by native_decide
  have hR : n₁_x7 ≤ m0 ^ 2 + (x7 : ℕ) * m0 + m0 := by native_decide
  simp [K, x7]; exact ⟨hL, hR⟩

lemma n₂_x7_in_block : n₂_x7 ∈ K m0 (x7 : ℕ) := by
  have hL : m0 ^ 2 + (x7 : ℕ) * m0 + 1 ≤ n₂_x7 := by native_decide
  have hR : n₂_x7 ≤ m0 ^ 2 + (x7 : ℕ) * m0 + m0 := by native_decide
  simp [K, x7]; exact ⟨hL, hR⟩

def W7 : WitnessPkg x7 :=
  { n1 := n₁_x7, n2 := n₂_x7
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x7_in_block
  , in_block2 := n₂_x7_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case7_no_axioms :
    ((PhiGE (m0*m0 + (x7:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x7:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x7 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x7 W7


-- ------ Bloco x = 8 -------
def x8 : Fin 9 := ⟨8, by decide⟩
def n₁_x8 : ℕ := 353364821
def n₂_x8 : ℕ := 353364829

lemma n₁_x8_in_block : n₁_x8 ∈ K m0 (x8 : ℕ) := by
  have hL : m0 ^ 2 + (x8 : ℕ) * m0 + 1 ≤ n₁_x8 := by native_decide
  have hR : n₁_x8 ≤ m0 ^ 2 + (x8 : ℕ) * m0 + m0 := by native_decide
  simp [K, x8]; exact ⟨hL, hR⟩

lemma n₂_x8_in_block : n₂_x8 ∈ K m0 (x8 : ℕ) := by
  have hL : m0 ^ 2 + (x8 : ℕ) * m0 + 1 ≤ n₂_x8 := by native_decide
  have hR : n₂_x8 ≤ m0 ^ 2 + (x8 : ℕ) * m0 + m0 := by native_decide
  simp [K, x8]; exact ⟨hL, hR⟩

def W8 : WitnessPkg x8 :=
  { n1 := n₁_x8, n2 := n₂_x8
  , prime_n1 := by native_decide
  , prime_n2 := by native_decide
  , in_block1 := n₁_x8_in_block
  , in_block2 := n₂_x8_in_block
  , ge_succ1 := by native_decide
  , ge_succ2 := by native_decide
  , ne12     := by native_decide }

theorem phiDiff_ge_row_finalLowerLo_18794_case8_no_axioms :
    ((PhiGE (m0*m0 + (x8:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x8:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x8 : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_of x8 W8


/-- Versão auxiliar por pattern-matching: escolhe diretamente o caso certo. -/
private def phiDiff_ge_row_finalLowerLo_18794_ALL_aux
  : (x : Fin 9) →
    ((PhiGE (m0*m0 + (x:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x : ℝ)
| ⟨0,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case0_no_axioms
| ⟨1,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case1_no_axioms
| ⟨2,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case2_no_axioms
| ⟨3,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case3_no_axioms
| ⟨4,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case4_no_axioms
| ⟨5,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case5_no_axioms
| ⟨6,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case6_no_axioms
| ⟨7,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case7_no_axioms
| ⟨8,  _⟩ => phiDiff_ge_row_finalLowerLo_18794_case8_no_axioms

/-- Versão “ALL”: para todo x=0..8, vale o bound do certificado. -/
theorem phiDiff_ge_row_finalLowerLo_18794_ALL (x : Fin 9) :
    ((PhiGE (m0*m0 + (x:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (finalLowerLo_of x : ℝ) :=
  phiDiff_ge_row_finalLowerLo_18794_ALL_aux x

 #print axioms RoughBlocks.External.Certs.phiDiff_ge_row_finalLowerLo_18794_ALL



/-- Versão racional: cada valor do certificado uniforme é ≤ o `finalLowerLo` do rows. -/
lemma uniformLB_le_rows_q (x : Fin 9) :
    uniformLB18794_finalLowerLo x ≤ finalLowerLo_of x := by
  -- abre os 9 casos e deixa o kernel comparar os racionais
  fin_cases x <;>
    (dsimp [uniformLB18794_finalLowerLo, finalLowerLo_of, idx, rows18794_length]; native_decide)

 #print axioms RoughBlocks.External.Certs.uniformLB_le_rows_q


/-- Versão em ℝ (cast do resultado racional). -/
lemma uniformLB_le_rows (x : Fin 9) :
    (uniformLB18794_finalLowerLo x : ℝ) ≤ (finalLowerLo_of x : ℝ) := by
  exact_mod_cast uniformLB_le_rows_q x

 #print axioms RoughBlocks.External.Certs.uniformLB_le_rows


/-- Teorema uniforme em m = 18794: para todo x=0..8, `Φ-dif ≥ uniformLB(x)`. -/
theorem phiDiff_ge_uniformLB_18794_ALL (x : Fin 9) :
    ((PhiGE (m0*m0 + (x:ℕ)*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + (x:ℕ)*m0)       (m0+1) : ℝ))
    ≥ (uniformLB18794_finalLowerLo x : ℝ) := by
  -- temos uniformLB ≤ finalLowerLo (lemma acima) e Φ-dif ≥ finalLowerLo (seu ALL)
  have h₁ := uniformLB_le_rows x
  have h₂ := phiDiff_ge_row_finalLowerLo_18794_ALL x
  exact le_trans h₁ h₂

 #print axioms RoughBlocks.External.Certs.phiDiff_ge_uniformLB_18794_ALL


theorem phiDiff_ge_uniformLB_18794_ALL_nat (x : ℕ) (hx : x ≤ 8) :
    ((PhiGE (m0*m0 + x*m0 + m0) (m0+1) : ℝ)
     - (PhiGE (m0*m0 + x*m0)       (m0+1) : ℝ))
    ≥ (uniformLB18794_finalLowerLo ⟨x, Nat.lt_succ_of_le hx⟩ : ℝ) := by
  simpa using phiDiff_ge_uniformLB_18794_ALL ⟨x, Nat.lt_succ_of_le hx⟩

 #print axioms RoughBlocks.External.Certs.phiDiff_ge_uniformLB_18794_ALL_nat


-- VERSÕES ARTERNATIVAS --
-- /-- Versão “ALL” em `m = m0` descendo de `rows` para o `uniformLB`. -/
-- theorem phiDiff_ge_uniformLB_18794_ALL (x : Fin 9) :
--     ((PhiGE (m0*m0 + (x:ℕ)*m0 + m0) (m0+1) : ℝ)
--      - (PhiGE (m0*m0 + (x:ℕ)*m0)       (m0+1) : ℝ))
--     ≥ (uniformLB18794_finalLowerLo x : ℝ) := by
--   -- Já provamos: Φ-dif ≥ rows(x)
--   have h_rows : ((PhiGE (m0*m0 + (x:ℕ)*m0 + m0) (m0+1) : ℝ)
--                  - (PhiGE (m0*m0 + (x:ℕ)*m0)       (m0+1) : ℝ))
--                 ≥ (finalLowerLo_of x : ℝ) :=
--     phiDiff_ge_row_finalLowerLo_18794_ALL x
--   -- E do “bridge” uniform: uniformLB(x) ≤ rows(x)
--   have h_cmp : (uniformLB18794_finalLowerLo x : ℝ) ≤ (finalLowerLo_of x : ℝ) :=
--     uniformLB_le_rows x
--   -- Conclusão por transitividade
--   exact le_trans h_cmp h_rows

-- #print axioms RoughBlocks.External.Certs.phiDiff_ge_uniformLB_18794_ALL

-- VERSÕES ARTERNATIVAS --
-- /-- Wrapper em ℕ: usa `x ≤ 8` para converter em `Fin 9`. -/
-- theorem phiDiff_ge_uniformLB_18794_ALL_nat (x : ℕ) (hx : x ≤ 8) :
--     ((PhiGE (m0*m0 + x*m0 + m0) (m0+1) : ℝ)
--      - (PhiGE (m0*m0 + x*m0)     (m0+1) : ℝ))
--     ≥ (uniformLB18794_finalLowerLo ⟨x, Nat.lt_succ_of_le hx⟩ : ℝ) := by
--   simpa using phiDiff_ge_uniformLB_18794_ALL ⟨x, Nat.lt_succ_of_le hx⟩

-- #print axioms RoughBlocks.External.Certs.phiDiff_ge_uniformLB_18794_ALL_nat


end RoughBlocks.External.Certs
