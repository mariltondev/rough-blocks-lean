/-
SPDX-License-Identifier: Apache-2.0
(c) 2025 Marilton Costa Ribeiro

Row0 (1e6): remove o axioma `phiDiff_ge_row_finalLowerLo_*` para x = 0.
Prova "Φ-dif(m,0) ≥ finalLowerLo(row0)" a partir de um certificado POR-LINHA
que fornece um bound direto em `countRoughInBlock m 0` (sem passar por LB),
agora com limiar `m ≥ 1_000_000` e nomes atualizados.
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

/-- Valor racional do "finalLowerLo" da linha 0 no certificado.
    ⟵ Substitua este valor pelo do seu artefato Julia, se quiser fixar. -/
def q0 : ℚ := (row0.finalLowerLo : ℚ)   -- por padrão, use o próprio campo; troque se quiser fixar

/-- **Certificado por-linha (Row 0, 1e6)**, em lógica pura:
  1) o `finalLowerLo` realmente coincide com `q0` (no tipo ℚ);
  2) para todo `m ≥ 1_000_000`, a contagem no bloco 0 é ≥ `q0` (em ℝ).
  OBS: isso é exatamente o que sua pipeline Julia deve testemunhar. -/
structure Row0Certificate : Prop :=
  (finalLo_is_q : (row0.finalLowerLo : ℚ) = q0)
  (count_ge_q   : ∀ {m : ℕ}, 1000000 ≤ m → (countRoughInBlock m 0 : ℝ) ≥ (q0 : ℝ))

/-- **Teorema (Row 0, limiar 1e6, sem axioma):**
    Do certificado acima, conclui-se `Φ-dif(m,0) ≥ finalLowerLo(row0)` para todo `m ≥ 1_000_000`. -/
@[simp]
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

/-!
Como usar:

1) Gere (via Julia) as igualdades/inequações exatas que dão `Row0Certificate`
   com o limiar `m ≥ 1_000_000`.
2) Em um arquivo `Row0_Certificate_1e6.lean`, forneça uma instância/lemma que
   produza `Row0Certificate` a partir do seu artefato numérico.
3) Importe esse arquivo aqui e aplique o teorema
   `phiDiff_ge_row0_finalLowerLo_1e6_of_certificate`.

Se preferir prender `q0` a um racional literal, basta substituir a definição
`q0` por esse literal e ajustar `finalLo_is_q` no certificado.
-/

end RoughBlocks.External.Certs
