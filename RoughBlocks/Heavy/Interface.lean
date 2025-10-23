/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Defs

/-
Interface “leve” consumida pelos módulos Heavy:

* Enunciado canônico `ExistsInBlockStmt` (“existe um m-áspero em cada bloco”);
* Limiar técnico `U0Default` (paper) e limiar **real** `BridgeThreshold` (= 18794);
* Constantes `C0Default`, `C1Default`, `C2Default` (alinhadas ao paper);
* Versões discreta e real da contagem na janela (X, X+Y].

Observações:
- `C1Default` é `noncomputable` pois é introduzida como racional→real.
- `C2Default` é natural (frequentemente coerido para `ℝ` nos módulos analíticos).
- As janelas seguem a convenção `(X, X+Y] = { n | X < n ≤ X+Y }`.
-/

namespace RoughBlocks.Heavy

/--
`ExistsInBlockStmt threshold` formaliza o esquema:
> Para todo `m ≥ threshold` e todo deslocamento curto `x ≤ 8`,
> existe `n ∈ K m x` tal que `mRough m n`.

Aqui, `K m x` é a janela aritmética definida em `RoughBlocks.Defs`, e
`mRough` é a propriedade “m-áspero”.
-/
def ExistsInBlockStmt (threshold : ℕ) : Prop :=
  ∀ m x : ℕ, m ≥ threshold → x ≤ 8 →
    ∃ n : ℕ, n ∈ RoughBlocks.K m x ∧ RoughBlocks.mRough m n

/-- Limiar técnico mínimo para os insumos analíticos (Mertens etc.). -/
def U0Default : ℕ := 1000

/-- Limiar **real** do certificado uniforme (conforme o paper): 18 794. -/
def BridgeThreshold : ℕ := 18794

/-- Alvo padrão do projeto: existe um m-áspero em cada bloco a partir do limiar real. -/
abbrev ExistsInBlock : Prop := ExistsInBlockStmt BridgeThreshold

/-- Constantes das estimativas (alinhadas ao paper). -/
def C0Default : ℝ := (2 : ℝ)
noncomputable def C1Default : ℝ := ((22 : ℚ) / 5 : ℝ)
def C2Default : ℕ := 100

/--
Contagem discreta na janela `(X, X+Y]`: número de `n` tais que
`X < n ≤ X+Y` e `mRough y n`.

Observações:
- Para `Y = 0`, o intervalo é vazio (contagem `0`).
- Implementação via `Finset.Icc (X+1) (X+Y)` seguida de `filter`.
-/
noncomputable def countWindow (y X Y : ℕ) : ℕ := by
  classical
  exact (((Finset.Icc (X + 1) (X + Y))).filter (fun n : ℕ => RoughBlocks.mRough y n)).card

/-- Versão em `ℝ` da contagem discreta `countWindow`. -/
noncomputable def lowerBoundCount (y X Y : ℕ) : ℝ := (countWindow y X Y : ℝ)

/-! Sanidades fechadas (não dependem do ambiente): -/

/-- Fato elementar: `U0Default ≥ 2`. Útil para descarregar hipóteses `m ≥ 2`. -/
lemma U0Default_ge_two : (2 : ℕ) ≤ U0Default := by decide

/-- `U0Default ≤ BridgeThreshold` (garante que o limiar analítico fica bem abaixo do limiar real). -/
lemma U0Default_le_BridgeThreshold : U0Default ≤ BridgeThreshold := by decide

@[simp] lemma U0Default_def       : U0Default       = 1000  := rfl
@[simp] lemma BridgeThreshold_def : BridgeThreshold  = 18794 := rfl
@[simp] lemma C0Default_def       : C0Default       = (2 : ℝ) := rfl
@[simp] lemma C1Default_def       : C1Default       = (22 : ℝ) / 5 := rfl
@[simp] lemma C2Default_def       : C2Default       = 100 := rfl

end RoughBlocks.Heavy
