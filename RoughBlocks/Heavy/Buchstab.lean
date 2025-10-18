/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Heavy.Buchstab.Core
import RoughBlocks.Heavy.Identity

/-!
# Buchstab (re-export)

Camada fina que **reexporta** as definições centrais de Buchstab de `Core.lean`
e adiciona somente **lemas de conveniência** de baixo acoplamento.

## Conteúdo

* `isRoughGT_one`  – por convenção, `1` é áspero(> `y`) para todo `y`.
* `isRoughGE_one`  – por convenção, `1` é áspero(≥ `p`) para todo `p`.
* `isRoughGE_mono_param` – **monotonicidade** no parâmetro: se `p ≤ q` e `n` é áspero(≥ `q`),
  então `n` é áspero(≥ `p`).

> Observação: As definições `isRoughGT` e `isRoughGE` vêm de `Buchstab.Core`.
> Aqui não introduzimos dependências matemáticas adicionais — apenas fatos básicos
> amplamente reutilizados em provas posteriores.
-/

namespace RoughBlocks.Heavy

/--
Fato de normalização: por **convenção**, `1` é permitido como áspero(> `y`)
para qualquer `y : ℕ`. Corresponde ao caso `Or.inl rfl` na definição.
-/
@[simp] lemma isRoughGT_one (y : ℕ) : isRoughGT y 1 := Or.inl rfl

/--
Fato de normalização: por **convenção**, `1` é permitido como áspero(≥ `p`)
para qualquer `p : ℕ`. Corresponde ao caso `Or.inl rfl` na definição.
-/
@[simp] lemma isRoughGE_one (p : ℕ) : isRoughGE p 1 := Or.inl rfl

/-- Reexport leve: monotonicidade de `PhiGE` no primeiro argumento (prova em `Identity`). -/
theorem PhiGE_mono_in_X' (p : ℕ) : Monotone (fun N => PhiGE N p) :=
  PhiGE_mono_in_X p

/--
**Monotonicidade no parâmetro (versão ≥):** se `p ≤ q` e `n` é `isRoughGE q n`,
então também `isRoughGE p n`.

Intuição: exigir que todos os fatores primos de `n` sejam `≥ q` é mais forte
do que exigir `≥ p` quando `p ≤ q`; logo a propriedade é preservada ao diminuir
o limiar.
-/
lemma isRoughGE_mono_param {p q n : ℕ}
    (hpq : p ≤ q) (hn : isRoughGE q n) : isRoughGE p n := by
  rcases hn with rfl | ⟨hn2, hmin⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨hn2, hpq.trans hmin⟩

end RoughBlocks.Heavy
