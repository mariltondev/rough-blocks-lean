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
# Buchstab/Core — definições unificadas

Neste módulo ficam **apenas** as definições básicas e lemas estruturais
de baixo nível:

* `smallestPrimeFactor`
* predicados `isRoughGT` (>) e `isRoughGE` (≥)
* decidibilidade dos predicados
* `primesIn`
* `PhiGT`, `PhiGE`  (**convencionalizamos `PhiGE` com `Icc 1 X` e `≥`**)
* `countRoughNat`
* `ω` (apenas a forma usada)
* `PhiGE_mono_X` (monotonicidade em `X`)

Lemas de janelas e identidades telescópicas ficam em `WindowLink/Core.lean`.
-/

namespace RoughBlocks.Heavy
open scoped BigOperators
open Finset

/-- Menor fator primo canônico (0/1 tratados à parte). -/
def smallestPrimeFactor (n : ℕ) : ℕ :=
  if h0 : n = 0 then 0
  else if h1 : n = 1 then 1
  else Nat.minFac n

/-- Versão (simples) de Buchstab para `u ∈ [1,3]`. -/
noncomputable def ω (u : ℝ) : ℝ :=
  if u < 1 then 0
  else if u ≤ 2 then 1 / u
  else if u ≤ 3 then (1 + Real.log (u - 1)) / u
  else 0

/-! ## Predicados `y`-rough -/

/-- Condição **estrita**: `n = 1` ou (`n ≥ 2` ∧ `minFac n > y`). -/
def isRoughGT (y n : ℕ) : Prop :=
  n = 1 ∨ (2 ≤ n ∧ Nat.minFac n > y)

/-- Condição **larga**: `n = 1` ou (`n ≥ 2` ∧ `minFac n ≥ y`). -/
def isRoughGE (y n : ℕ) : Prop :=
  n = 1 ∨ (2 ≤ n ∧ Nat.minFac n ≥ y)

/-- Decidibilidade para `isRoughGT`. -/
instance (y : ℕ) : DecidablePred (isRoughGT y) := by
  classical
  intro n; unfold isRoughGT; infer_instance

/-- Decidibilidade para `isRoughGE`. -/
instance (y : ℕ) : DecidablePred (isRoughGE y) := by
  classical
  intro n; unfold isRoughGE; infer_instance

/-- Primos `p` em `y < p ≤ X`. -/
def primesIn (y X : ℕ) : Finset ℕ :=
  (Finset.Icc (y + 1) X).filter Nat.Prime

/-! ## Contagens -/

/-- `Φ_GT(X,y)`: números `1 ≤ n ≤ X` com `isRoughGT y n`. -/
def PhiGT (X y : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)).card

/-- `Φ_GE(X,y)`: **convencionado** aqui como
    números `1 ≤ n ≤ X` com `isRoughGE y n` (predicado com `≥`). -/
def PhiGE (X y : ℕ) : ℕ :=
  ((Finset.Icc 1 X).filter (fun n => isRoughGE y n)).card

/-- Contagem em janela `(X, X+Y]` sob a condição **estrita**. -/
def countRoughNat (y X Y : ℕ) : ℕ :=
  ((Finset.Icc (X + 1) (X + Y)).filter (fun n => isRoughGT y n)).card

/-! ## Lemas básicos -/

/-- `Φ_GT` é monótona em `X`. -/
lemma PhiGT_mono_X {X₁ X₂ y : ℕ} (h : X₁ ≤ X₂) :
    PhiGT X₁ y ≤ PhiGT X₂ y := by
  classical
  unfold PhiGT
  refine Finset.card_le_card ?_
  intro n hn
  rcases mem_filter.1 hn with ⟨hnI, hprop⟩
  rcases mem_Icc.1 hnI with ⟨h1, hX⟩
  have : n ∈ Finset.Icc 1 X₂ := mem_Icc.mpr ⟨h1, le_trans hX h⟩
  exact mem_filter.mpr ⟨this, hprop⟩

/-- `Φ_GE` é monótona em `X`: se `X₁ ≤ X₂`, então `PhiGE X₁ y ≤ PhiGE X₂ y`. -/
lemma PhiGE_mono_X {X₁ X₂ y : ℕ} (h : X₁ ≤ X₂) :
    PhiGE X₁ y ≤ PhiGE X₂ y := by
  classical
  -- PhiGE X y := ((Icc 1 X).filter (fun n => isRoughGE y n)).card
  refine Finset.card_le_card ?_
  intro n hn
  rcases mem_filter.1 hn with ⟨hnI, hprop⟩
  rcases mem_Icc.1 hnI with ⟨h1, hX⟩
  have : n ∈ Finset.Icc 1 X₂ := by
    exact mem_Icc.mpr ⟨h1, le_trans hX h⟩
  exact mem_filter.mpr ⟨this, hprop⟩

/-- De `isRoughGT y n` obtemos a condição “todos os primos divisores de `n` são `> y`”
no estilo do seu `mRough`. -/
lemma mRough_of_isRoughGT (y n : ℕ) :
    isRoughGT y n → mRough y n := by
  classical
  intro h p hpPrime hp_dvd
  rcases h with h1 | ⟨hn2, hmin⟩
  · have : ¬ p ∣ 1 := hpPrime.not_dvd_one
    exact (this (by simpa [h1] using hp_dvd)).elim
  · have hp2 : 2 ≤ p := hpPrime.two_le
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
  ·
    have h2 : 2 ≤ n := by
      have : 1 < n := lt_of_le_of_ne hn1 (fun hne => h1 (Eq.symm hne))
      exact Nat.succ_le_of_lt this
    set q := Nat.minFac n
    have hqprime : Nat.Prime q := Nat.minFac_prime h1
    have hq_dvd  : q ∣ n := Nat.minFac_dvd n
    have hyq : y < q := h q hqprime hq_dvd
    exact Or.inr ⟨h2, hyq⟩

/-- Equivalência útil quando `1 ≤ n`. -/
lemma isRoughGT_iff_mRough_of_pos (y n : ℕ) (hn1 : 1 ≤ n) :
    isRoughGT y n ↔ mRough y n := by
  constructor
  · exact mRough_of_isRoughGT y n
  · intro h; exact isRoughGT_of_mRough_of_pos y n hn1 h

end RoughBlocks.Heavy
