/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib

open Finset

/-!
# RoughBlocks.Defs

Núcleo de **definições públicas** do projeto.

Este módulo é intencionalmente mínimo: reúne apenas nomes e tipos usados
pelas demais camadas. Não introduz axiomas, depende apenas de `Mathlib` e
foi pensado para permanecer **estável** enquanto as camadas superiores evoluem.

## Conteúdo

* `mRough` — predicado “`m`-áspero”: todo primo que divide `n` é `> m`.
* `K` — bloco discreto `K(m, x)` como intervalo finito fechado em `ℕ`.
* `BlockHasMRough` — existência de um elemento `m`-áspero dentro do bloco.
* `roughSetInBlock` / `countRoughInBlock` — conjunto e contagem de `m`-ásperos no bloco.
* `exists_of_count_ge_one` — se a contagem é ≥ 1, então existe um elemento no bloco.

## Notas de uso

* Por convenção, “áspero” aqui é **estritamente** maior que o limiar (`> m`).
* Para `n = 1`, `mRough m 1` é verdadeiro por vacuidade (nenhum primo divide `1`).
* O bloco `K(m, x)` tem **tamanho exatamente `m`** e representa a janela
  `[m^2 + x·m + 1, m^2 + (x+1)·m] ∩ ℕ`.
-/

namespace RoughBlocks

/-- `mRough m n` significa que **todo primo** `p` que divide `n` satisfaz `m < p`.

Observação: quando `n ≥ 2`, isto é equivalente a `Nat.minFac n > m`. Mantemos
a formulação por quantificação sobre primos para maximizar reuso em lemas
elementares sem forçar dependência em propriedades específicas de `minFac`. -/
def mRough (m n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → m < p

/-- Bloco discreto `K(m,x)` como `Finset ℕ`.

Representa o intervalo **fechado** (extremos inclusivos)
`{ m^2 + x·m + 1, …, m^2 + (x+1)·m }`. Em particular, `K(m,x)` tem
cardinalidade exatamente `m`. -/
def K (m x : ℕ) : Finset ℕ :=
  Finset.Icc (m^2 + x*m + 1) (m^2 + (x+1)*m)

/-- Predicado existencial: o bloco `K m x` contém **algum** número `m`-áspero. -/
def BlockHasMRough (m x : ℕ) : Prop :=
  ∃ n ∈ K m x, mRough m n

/-- Conjunto de elementos do bloco `K m x` que são `m`-ásperos.

`noncomputable` apenas porque recorremos a `classical` para decidir o filtro. -/
noncomputable def roughSetInBlock (m x : ℕ) : Finset ℕ := by
  classical
  exact (K m x).filter (mRough m)

/-- Contagem de `m`-ásperos no bloco `K m x`. -/
noncomputable def countRoughInBlock (m x : ℕ) : ℕ := by
  classical
  exact (roughSetInBlock m x).card

/-- Lema puramente combinatório: se a contagem é ≥ 1, então existe um elemento no bloco
que satisfaz `mRough`.

Sem axiomas: decorre de `Finset.card_pos` aplicado ao filtro que define `roughSetInBlock`. -/
lemma exists_of_count_ge_one {m x : ℕ}
  (h : countRoughInBlock m x ≥ 1) :
  ∃ n ∈ K m x, mRough m n := by
  classical
  -- 1 ≤ card ↔ 0 < card
  have hpos : 0 < (roughSetInBlock m x).card := by
    -- `Nat.succ_le_iff` reescreve `1 ≤ n` como `0 < n`
    simpa [countRoughInBlock, Nat.succ_le_iff] using h
  -- `card_pos` dá um elemento do conjunto filtrado
  rcases card_pos.mp hpos with ⟨n, hn⟩
  have hnK   : n ∈ K m x := by
    simpa [roughSetInBlock, mem_filter] using (mem_filter.mp hn).1
  have hnRgh : mRough m n := by
    simpa [roughSetInBlock, mem_filter] using (mem_filter.mp hn).2
  exact ⟨n, hnK, hnRgh⟩

end RoughBlocks
