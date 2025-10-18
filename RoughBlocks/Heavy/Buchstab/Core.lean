/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Heavy.Buchstab.MinFac
import RoughBlocks.Defs

/-!
# Núcleo de Buchstab (definições)

Este arquivo fixa as duas noções de `y`-rough usadas no projeto:

* `isRoughGT y n` — condição **estrita** (`minFac n > y`), adequada para a contagem
  de números `y`-ásperos.
* `isRoughGE y n` — condição **larga** (`minFac n ≥ y`), usada no passo recursivo
  na identidade de Buchstab.

Além disso, introduzimos:
* `PhiGT`, `PhiGE` — contagens prefixo (até `X`) sob as condições acima;
* `primesIn` — primos `p` no recorte `y < p ≤ X`;
* `countRoughNat` — contagem em janela `(X, X+Y]` sob a condição estrita.

> As provas combinatórias mais pesadas (identidade de Buchstab, truncagens etc.)
> ficam em arquivos separados; aqui mantemos apenas as definições básicas e lemas
> elementares/estruturais.
-/

namespace RoughBlocks.Heavy
open scoped BigOperators
open Finset

/-! ## Definições principais -/

/-- Condição **estrita**: `n = 1` **ou** `n ≥ 2` com `minFac n > y`. -/
def isRoughGT (y n : ℕ) : Prop :=
  n = 1 ∨ (2 ≤ n ∧ Nat.minFac n > y)

/-- Condição **larga**: `n = 1` **ou** `n ≥ 2` com `minFac n ≥ y`. -/
def isRoughGE (y n : ℕ) : Prop :=
  n = 1 ∨ (2 ≤ n ∧ Nat.minFac n ≥ y)

/-- Predicado decidível para `isRoughGT y`. Útil em `filter` / somas finitas. -/
instance (y : ℕ) : DecidablePred (isRoughGT y) := by
  classical
  intro n; unfold isRoughGT; infer_instance

/-- Predicado decidível para `isRoughGE y`. Útil em `filter` / somas finitas. -/
instance (y : ℕ) : DecidablePred (isRoughGE y) := by
  classical
  intro n; unfold isRoughGE; infer_instance

/-- Primos `p` com `y < p ≤ X`. -/
def primesIn (y X : ℕ) : Finset ℕ :=
  (Finset.Icc (y + 1) X).filter Nat.Prime

/-- Contagem prefixo **estrita**: números `n ≤ X` com `isRoughGT y n`. -/
def PhiGT (X y : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)).card

/-- Contagem prefixo **larga**: números `n ≤ X` com `isRoughGE y n`. -/
def PhiGE (X y : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => isRoughGE y n)).card

/-- Contagem em janela `(X, X+Y]` sob a condição **estrita**. -/
def countRoughNat (y X Y : ℕ) : ℕ :=
  ((Finset.Icc (X + 1) (X + Y)).filter (fun n => isRoughGT y n)).card

/-! ## Lemas básicos (monotonicidade em `X`) -/

/-- `PhiGT` é monótona em `X`: se `X₁ ≤ X₂`, então `PhiGT X₁ y ≤ PhiGT X₂ y`. -/
lemma PhiGT_mono_X {X₁ X₂ y : ℕ} (h : X₁ ≤ X₂) :
    PhiGT X₁ y ≤ PhiGT X₂ y := by
  classical
  refine Finset.card_le_card ?_
  intro n hn
  rcases mem_filter.1 hn with ⟨hnI, hprop⟩
  rcases mem_Icc.1 hnI with ⟨h1, hX⟩
  have : n ∈ Finset.Icc 1 X₂ := by
    exact mem_Icc.mpr ⟨h1, le_trans hX h⟩
  exact mem_filter.mpr ⟨this, hprop⟩

/-- `PhiGE` é monótona em `X`: se `X₁ ≤ X₂`, então `PhiGE X₁ y ≤ PhiGE X₂ y`. -/
lemma PhiGE_mono_X {X₁ X₂ y : ℕ} (h : X₁ ≤ X₂) :
    PhiGE X₁ y ≤ PhiGE X₂ y := by
  classical
  refine Finset.card_le_card ?_
  intro n hn
  rcases mem_filter.1 hn with ⟨hnI, hprop⟩
  rcases mem_Icc.1 hnI with ⟨h1, hX⟩
  have : n ∈ Finset.Icc 1 X₂ := by
    exact mem_Icc.mpr ⟨h1, le_trans hX h⟩
  exact mem_filter.mpr ⟨this, hprop⟩

/-- De `isRoughGT y n` obtemos `mRough y n` (a versão “todos os primos divisores > y”). -/
lemma mRough_of_isRoughGT (y n : ℕ) :
    isRoughGT y n → mRough y n := by
  classical
  intro h p hpPrime hp_dvd
  rcases h with h1 | ⟨hn2, hmin⟩
  · -- Caso `n = 1`: nenhum primo divide `1` (contradição se ocorresse).
    have : ¬ p ∣ 1 := hpPrime.not_dvd_one
    exact (this (by simpa [h1] using hp_dvd)).elim
  · -- Caso `n ≥ 2`: se `p ∣ n` e `p` é primo, então `minFac n ≤ p`.
    have hp2 : 2 ≤ p := hpPrime.two_le
    have hmin_le_p : Nat.minFac n ≤ p :=
      Nat.minFac_le_of_dvd hp2 hp_dvd
    exact lt_of_lt_of_le hmin hmin_le_p

/-- De `mRough y n` e `1 ≤ n`, obtemos `isRoughGT y n`. -/
lemma isRoughGT_of_mRough_of_pos (y n : ℕ) (hn1 : 1 ≤ n) :
    mRough y n → isRoughGT y n := by
  classical
  intro h
  by_cases h1 : n = 1
  · exact Or.inl h1
  · -- Aqui `n ≠ 1` e `n ≥ 2`.
    have h2 : 2 ≤ n := by
      have : 1 < n := lt_of_le_of_ne hn1 (fun hne => h1 (Eq.symm hne))
      exact Nat.succ_le_of_lt this
    -- Tome `q = minFac n`, que é primo e divide `n`; aplique `mRough` em `q`.
    set q := Nat.minFac n
    have hqprime : Nat.Prime q := Nat.minFac_prime h1
    have hq_dvd  : q ∣ n := Nat.minFac_dvd n
    have hyq : y < q := h q hqprime hq_dvd
    exact Or.inr ⟨h2, hyq⟩

/-- Equivalência útil quando sabemos `1 ≤ n`. -/
lemma isRoughGT_iff_mRough_of_pos (y n : ℕ) (hn1 : 1 ≤ n) :
    isRoughGT y n ↔ mRough y n := by
  constructor
  · exact mRough_of_isRoughGT y n
  · intro h; exact isRoughGT_of_mRough_of_pos y n hn1 h

end RoughBlocks.Heavy
