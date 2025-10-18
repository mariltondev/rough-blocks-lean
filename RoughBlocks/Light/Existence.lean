/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Light.Export
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.External.BridgeUniform

open RoughBlocks

namespace RoughBlocks.Light

/-- Do bloco para o formato “de–até” com primos grandes.

Se existe `n ∈ K m x` tal que `mRough m n`, então existe `n` no intervalo
`[m^2 + x m + 1, m^2 + (x+1) m]` e todo primo que divide `n` é `≥ m`.

Este lema é puramente elementar (apenas desenrola `K` e `mRough`). -/
theorem of_block_to_interval_primes
  {m x : ℕ}
  (h : ∃ n ∈ K m x, mRough m n) :
  ∃ n,
    m ^ 2 + x * m + 1 ≤ n ∧
    n ≤ m ^ 2 + (x + 1) * m ∧
    ∀ p : ℕ, p.Prime → p ∣ n → m ≤ p := by
  rcases h with ⟨n, hnK, hnR⟩
  -- abrir a membresia no bloco
  have hIcc : n ∈ Finset.Icc (m^2 + x*m + 1) (m^2 + (x+1)*m) := by
    simpa [K, pow_two, Nat.mul_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc,
           Nat.mul_comm] using hnK
  rcases Finset.mem_Icc.1 hIcc with ⟨hL, hR⟩
  -- da aspereza obtemos `m < p` ⇒ `m ≤ p`
  have hprime : ∀ p : ℕ, p.Prime → p ∣ n → m ≤ p := by
    intro p hp hdiv
    exact (hnR p hp hdiv).le
  exact ⟨n, hL, hR, hprime⟩

/-- Varredura determinística: para `2 ≤ m ≤ 10⁶` e `x ≤ 8`,
há pelo menos um `m`-áspero no bloco `K m x`.
Fonte: artefato computacional no Zenodo (DOI `10.5281/zenodo.17137291`). -/
axiom budget_verified_by_scan
  {m x : ℕ} (hm₂ : 2 ≤ m) (hm_top : m ≤ 1_000_000) (hx : x ≤ 8) :
  RoughBlocks.countRoughInBlock m x ≥ 1

/-- Existência para todo `m ≥ 10⁶`, usando a ponte uniforme externa. -/
theorem existence_ge_1e6_uniform
  {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
  ∃ n,
    m ^ 2 + x * m + 1 ≤ n ∧
    n ≤ m ^ 2 + (x + 1) * m ∧
    ∀ p : ℕ, p.Prime → p ∣ n → m ≤ p := by
  -- ponte (LB ≤ contagem) vinda do certificado externo
  have hBridge := RoughBlocks.External.bridge_ge_1e6_uniform (m := m) (x := x) hm hx
  -- fachada Light já sabe transformar "LB ≥ 1" + ponte → existência no bloco
  have hBlock : ∃ n ∈ K m x, mRough m n :=
    RoughBlocks.Light.exist_in_block_ge_1e6_if_bridge (m := m) (x := x) hm hx hBridge
  -- traduz do bloco para o formato “de–até” + condição dos primos
  exact of_block_to_interval_primes hBlock

/-- Teorema principal de existência (faixa completa).
Para `m ≥ 2` e `x ≤ 8`, existe `n` no bloco `K m x`
tal que todos os primos que dividem `n` são `≥ m`.  Junta:
* `budget_verified_by_scan` para `2 ≤ m ≤ 10⁶`;
* `existence_ge_1e6_uniform` para `m ≥ 10⁶`. -/
theorem existence_main_all
  {m x : ℕ} (hm : 2 ≤ m) (hx : x ≤ 8) :
  ∃ n,
    m ^ 2 + x * m + 1 ≤ n ∧
    n ≤ m ^ 2 + (x + 1) * m ∧
    ∀ p : ℕ, p.Prime → p ∣ n → m ≤ p := by
  by_cases h : m < 1_000_000
  · -- caso “baixo”: 2 ≤ m ≤ 10^6  (via varredura determinística do Zenodo)
    have hm_top : m ≤ 1_000_000 := le_of_lt h
    have hCount : 1 ≤ RoughBlocks.countRoughInBlock m x :=
      budget_verified_by_scan (hm₂ := hm) (hm_top := hm_top) (hx := hx)
    have hBlock : ∃ n ∈ RoughBlocks.K m x, RoughBlocks.mRough m n :=
      RoughBlocks.exists_of_count_ge_one hCount
    exact RoughBlocks.Light.of_block_to_interval_primes hBlock
  · -- caso “alto”: m ≥ 10^6  (via ponte uniforme + parte formal)
    have hm_ge : 1_000_000 ≤ m := Nat.le_of_not_lt h
    exact RoughBlocks.Light.existence_ge_1e6_uniform (m := m) (x := x) hm_ge hx

-- teste rápido opcional (pode remover se quiser o arquivo 100% limpo):
example (m x : ℕ) (hm : 1_000_000 ≤ m) (hx : x ≤ 8) :
    ∃ n, m ^ 2 + x * m + 1 ≤ n ∧
         n ≤ m ^ 2 + (x + 1) * m ∧
         ∀ p : ℕ, p.Prime → p ∣ n → m ≤ p := by
  -- ponte uniforme (axioma externo) + existência no bloco
  have hBlock :
      ∃ n ∈ RoughBlocks.K m x, RoughBlocks.mRough m n :=
    RoughBlocks.Light.exist_in_block_ge_1e6_if_bridge
      (m := m) (x := x) hm hx
      (RoughBlocks.External.bridge_ge_1e6_uniform (m := m) (x := x) hm hx)
  -- traduz do bloco para o enunciado “de–até” com primos ≥ m
  exact RoughBlocks.Light.of_block_to_interval_primes hBlock

end RoughBlocks.Light
