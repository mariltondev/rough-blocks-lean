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
Este arquivo expõe a interface “leve” usada pelos módulos Heavy:

* Enunciado canônico `ExistsInBlockStmt` (“existe um m-áspero em cada bloco”);
* Constantes padrão `U0Default`, `C0Default`, `C1Default`, `C2Default` alinhadas ao paper;
* Versões discreta e real da contagem na janela (X, X+Y].

Observações:
- `C1Default` é `noncomputable` pois é introduzida como racional→real.
- `C2Default` é natural (frequentemente coerido para `ℝ` nos módulos analíticos).
- As janelas seguem a convenção `(X, X+Y] = { n | X < n ≤ X+Y }`.

Esta interface é estável e serve como “contrato” para as provas numéricas/analíticas.
Não altere as constantes sem atualizar as provas em `RoughBlocks.Heavy`.
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

/--
Limite inferior técnico a partir do qual os argumentos assintóticos passam a valer.
Mantido em sincronia com os módulos `Heavy.*`.
-/
def U0Default : ℕ := 1000

/-- Constante base usada nas estimativas (ver paper). -/
def C0Default : ℝ := (2 : ℝ)

/-- Constante de erro principal na forma analítica (ver paper). -/
noncomputable def C1Default : ℝ := ((22 : ℚ) / 5 : ℝ)

/-- Termo constante (buffer) nas cotas inferiores. -/
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

/--
Versão em `ℝ` da contagem discreta `countWindow`. Útil para integrar
as cotas analíticas (em `ℝ`) com a contagem em `ℕ`.
-/
noncomputable def lowerBoundCount (y X Y : ℕ) : ℝ := (countWindow y X Y : ℝ)

/-- Fato elementar: `U0Default ≥ 2`. Útil para descarregar hipóteses `m ≥ 2`. -/
lemma U0Default_ge_two : (2 : ℕ) ≤ U0Default := by decide

@[simp] lemma U0Default_def : U0Default = 1000 := rfl
@[simp] lemma C0Default_def : C0Default = (2 : ℝ) := rfl
@[simp] lemma C1Default_def : C1Default = (22 : ℝ) / 5 := rfl
@[simp] lemma C2Default_def : C2Default = 100 := rfl

end RoughBlocks.Heavy
