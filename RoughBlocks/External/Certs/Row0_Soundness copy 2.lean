/-
SPDX-License-Identifier: Apache-2.0
(c) 2025 Marilton Costa Ribeiro

Row0 (m ≥ 1e6): remove axiomas antigos e prova
Φ-dif(m,0) ≥ finalLowerLo(row0) a partir de um certificado POR-LINHA
que dá bound direto para countRoughInBlock m 0 (sem passar por LB).
-/

import Mathlib
import RoughBlocks.Heavy.WindowLink.Block            -- count ↔ Φ (janela curta)
import RoughBlocks.External.Certs.UniformGE1e6Bridge

noncomputable section
namespace RoughBlocks.External.Certs
open Classical Real
open RoughBlocks RoughBlocks.Heavy
open RoughBlocks.External.Certs.UniformGE1e6Bridge

/-- Atalho: Φ-dif na janela curta (def da camada Heavy). -/
abbrev PhiDiffAt (m x : ℕ) : ℝ := RoughBlocks.Heavy.PhiDiffAt m x

/-- Seleciona a linha `rows1e6` (tabela do certificado) correspondente a `x ≤ 8`. -/
def row1e6Of (x : ℕ) (hx : x ≤ 8) : BridgeRow :=
  -- `rows1e6` é uma lista literal com 9 entradas
  have hlen : rows1e6.length = 9 := by
    -- `simp` conhece o literal de `rows1e6` nesse módulo
    simp [rows1e6]
  have hxlt : x < rows1e6.length := by
    simpa [hlen] using Nat.lt_of_le_of_lt hx (by decide : 8 < 9)
  rows1e6.get ⟨x, hxlt⟩

/-- A linha do certificado para x = 0. -/
def row0 : BridgeRow :=
  row1e6Of 0 (by decide)

/-- Mantemos `q0` como alias para o valor do certificado. -/
def q0 : ℚ := (row0.finalLowerLo : ℚ)

/-- **Certificado por-linha (Row 0)**, em lógica pura:
  1) o `finalLowerLo` coincide com `q0` (no tipo ℚ);
  2) para todo `m ≥ 1e6`, a contagem no bloco 0 é ≥ `q0` (em ℝ). -/
structure Row0Certificate : Prop where
  finalLo_is_q : (row0.finalLowerLo : ℚ) = q0
  count_ge_q   : ∀ {m : ℕ}, 1000000 ≤ m → (countRoughInBlock m 0 : ℝ) ≥ (q0 : ℝ)

/-- **Teorema (Row 0, m ≥ 1e6):**
    Do certificado acima, conclui-se `Φ-dif(m,0) ≥ finalLowerLo(row0)` para todo `m ≥ 1e6`. -/
theorem phiDiff_ge_row0_finalLowerLo_1e6_of_certificate
  (hc : Row0Certificate) {m : ℕ} (hm : 1000000 ≤ m) :
  PhiDiffAt m 0 ≥ (row0.finalLowerLo : ℝ) := by
  -- janela curta: `count = Φ`
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ 1000000) hm
  have hx  : (0 : ℕ) ≤ 8 := by decide
  have hEq : (countRoughInBlock m 0 : ℝ) = PhiDiffAt m 0 := by
    -- a própria identidade count = Φ (sem .symm!)
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




/-! ----------------------------------------------------------------
    Row0: certificado concreto (sem axiomas), a partir do bridge.
    Basta fornecer a instância `Row0WindowLinkBound1e6` abaixo.
---------------------------------------------------------------- -/


/--
Forma **direta**, sem typeclass: se você já tem da pipeline o bound de janela curta
para x = 0 (isto é, para todo `m ≥ 1e6`, `countRoughInBlock m 0 ≥ row0.finalLowerLo`),
então obtemos `Φ-dif(m,0) ≥ 1`.
-/
theorem phiDiff_row0_ge_one_1e6_of_bound
  (hbound : ∀ {m : ℕ}, 1_000_000 ≤ m →
              (countRoughInBlock m 0 : ℝ) ≥ (row0.finalLowerLo : ℝ))
  {m : ℕ} (hm : 1_000_000 ≤ m) :
  PhiDiffAt m 0 ≥ (1 : ℝ) := by
  -- Constrói o certificado a partir do bound fornecido:
  let hc : Row0Certificate :=
    { finalLo_is_q := rfl
      count_ge_q := by
        intro m hm'
        simpa [q0] using (hbound hm') }
  -- Usa o seu teorema já provado + o fato numérico `finalLowerLo ≥ 1`.
  have hφ_ge_fl :
      PhiDiffAt m 0 ≥ (row0.finalLowerLo : ℝ) :=
    phiDiff_ge_row0_finalLowerLo_1e6_of_certificate hc hm
  have hfl_ge1 : (row0.finalLowerLo : ℝ) ≥ (1 : ℝ) :=
    row0_finalLowerLo_ge_one_real
  exact le_trans hfl_ge1 hφ_ge_fl

/--
Versão em termos de `count`: existe m-áspero no bloco 0 (pois `count ≥ 1`).
-/
theorem count_row0_ge_one_1e6_of_bound
  (hbound : ∀ {m : ℕ}, 1_000_000 ≤ m →
              (countRoughInBlock m 0 : ℝ) ≥ (row0.finalLowerLo : ℝ))
  {m : ℕ} (hm : 1_000_000 ≤ m) :
  (countRoughInBlock m 0 : ℝ) ≥ (1 : ℝ) := by
  -- Igualdade count = Φ na janela curta
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ 1_000_000) hm
  have hx  : (0 : ℕ) ≤ 8 := by decide
  have hEq : (countRoughInBlock m 0 : ℝ) = PhiDiffAt m 0 := by
    simpa [PhiDiffAt, RoughBlocks.Heavy.PhiDiffAt, Nat.zero_mul, zero_mul] using
      (countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := 0) hm2 hx)
  -- Conclusão via Φ ≥ 1
  have hφ : PhiDiffAt m 0 ≥ (1 : ℝ) :=
    phiDiff_row0_ge_one_1e6_of_bound hbound hm
  simpa [hEq, ge_iff_le] using hφ

/--
Se preferir registrar o bound uma vez só, crie uma **instância**.
Depois você pode usar as versões “noHyp” abaixo.
-/
class Row0WindowLinkBound1e6 : Prop where
  bound :
    ∀ {m : ℕ}, 1_000_000 ≤ m →
      (countRoughInBlock m 0 : ℝ) ≥ (row0.finalLowerLo : ℝ)

/-- Constrói automaticamente o `Row0Certificate` a partir da instância. -/
theorem row0_certificate_1e6 [Row0WindowLinkBound1e6] :
  Row0Certificate := by
  refine ⟨rfl, ?_⟩
  intro m hm
  have h := Row0WindowLinkBound1e6.bound (m := m) hm
  simpa [q0] using h

/-- Versão “sem passar hbound”, usando a instância. -/
theorem phiDiff_row0_ge_one_1e6_noHyp
  [Row0WindowLinkBound1e6] {m : ℕ} (hm : 1_000_000 ≤ m) :
  PhiDiffAt m 0 ≥ (1 : ℝ) := by
  -- usa o certificado induzido pela instância
  have hc : Row0Certificate := row0_certificate_1e6
  -- mesmo argumento do teorema direto
  have hφ_ge_fl :
      PhiDiffAt m 0 ≥ (row0.finalLowerLo : ℝ) :=
    phiDiff_ge_row0_finalLowerLo_1e6_of_certificate hc hm
  have hfl_ge1 : (row0.finalLowerLo : ℝ) ≥ (1 : ℝ) :=
    row0_finalLowerLo_ge_one_real
  exact le_trans hfl_ge1 hφ_ge_fl

/-- idem para `count`. -/
theorem count_row0_ge_one_1e6_noHyp
  [Row0WindowLinkBound1e6] {m : ℕ} (hm : 1_000_000 ≤ m) :
  (countRoughInBlock m 0 : ℝ) ≥ (1 : ℝ) := by
  -- count = Φ na janela curta
  have hm2 : 2 ≤ m := le_trans (by decide : 2 ≤ 1_000_000) hm
  have hx  : (0 : ℕ) ≤ 8 := by decide
  have hEq : (countRoughInBlock m 0 : ℝ) = PhiDiffAt m 0 := by
    simpa [PhiDiffAt, RoughBlocks.Heavy.PhiDiffAt, Nat.zero_mul, zero_mul] using
      (countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := 0) hm2 hx)
  have hφ : PhiDiffAt m 0 ≥ (1 : ℝ) := phiDiff_row0_ge_one_1e6_noHyp hm
  simpa [hEq, ge_iff_le] using hφ



end RoughBlocks.External.Certs
