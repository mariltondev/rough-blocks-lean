/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Heavy.WindowLink.Core
import RoughBlocks.Heavy.Interface

/-!
# Buchstab.Identity — versão segura (sem axiomas)

Formaliza as identidades de Buchstab (global e na janela) inteiramente em `ℕ`,
via famílias finitas e bijeções reais com `Finset.card_bij'`.
As versões em `ℝ` seguem por coerção e `Nat.cast_sub`, usando a monotonicidade
de `PhiGE` no primeiro argumento.
-/

namespace RoughBlocks.Heavy
open Finset
open scoped BigOperators
open RoughBlocks

@[simp] lemma PhiGE_zero (p : ℕ) : PhiGE 0 p = 0 := by
  simp [PhiGE]

/-- Classe do primo `p`: números `n ≤ X`, `n ≠ 1`, `y`-ásperos (modo estrito) e com fator mínimo `p`. -/
def classOf (X y p : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 X).filter fun n => n ≠ 1 ∧ isRoughGT y n ∧ Nat.minFac n = p)

/-- Fatores admissíveis para o primo `p`. -/
def factorSet (X p : ℕ) : Finset ℕ :=
  ((Finset.Icc 1 (X / p)).filter fun m => isRoughGE p m)

/-! ## Auxiliares básicos -/

/-- Desempacota `p ∈ (y, X]` juntamente com a primalidade. -/
lemma mem_primesIn {y X p : ℕ} :
    p ∈ primesIn y X ↔ y < p ∧ p ≤ X ∧ Nat.Prime p := by
  classical
  constructor
  · intro hp
    rcases Finset.mem_filter.1 hp with ⟨hpI, hpPrime⟩
    rcases Finset.mem_Icc.1 hpI with ⟨hp_lower, hp_upper⟩
    exact ⟨Nat.succ_le_iff.mp hp_lower, hp_upper, hpPrime⟩
  · intro h
    rcases h with ⟨hylt, hle, hp⟩
    exact Finset.mem_filter.2
      ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hylt, hle⟩, hp⟩

/-- Se `p` é primo e `isRoughGE p m`, então `minFac (p*m) = p`. -/
lemma minFac_mul_of_geRough {p m : ℕ}
    (hp : Nat.Prime p) (hmR : isRoughGE p m) : Nat.minFac (p * m) = p := by
  -- (≤) pois `p ∣ p*m` e `p ≥ 2`
  have hle : Nat.minFac (p * m) ≤ p :=
    minFac_le_of_prime_dvd hp ⟨m, by simp⟩
  -- (≥) pela minimalidade: qualquer primo de `p*m` é ≥ p
  have hge : p ≤ Nat.minFac (p * m) := by
    classical
    rcases hmR with rfl | ⟨hm2, hminm⟩
    · -- m = 1
      simp [hp.minFac_eq]
    ·
      set q := Nat.minFac (p * m)
      have hqprime : Nat.Prime q := by
        -- `p*m ≠ 1` pois `p ≥ 2` e `m ≥ 2`
        have hne1 : p * m ≠ 1 := by
          intro h
          have hp1 : 1 ≤ p := Nat.succ_le_of_lt hp.pos
          have : 2 ≤ p * m := by
            have : 2 * 1 ≤ m * p := Nat.mul_le_mul hm2 hp1
            simpa [Nat.mul_comm] using this
          have : (2 : ℕ) ≤ 1 := by simp [h] at this
          exact (Nat.not_succ_le_self 1) this
        simpa [q] using Nat.minFac_prime hne1
      have hq_dvd : q ∣ p * m := by simpa [q] using Nat.minFac_dvd (p * m)
      rcases (Nat.Prime.dvd_mul hqprime).1 hq_dvd with hqp | hqm
      · -- `q ∣ p` ⇒ `q = p` ⇒ `p ≤ q`
        have : q = p := by
          rcases (Nat.dvd_prime hp).1 hqp with hq1 | hqp'
          · exact (hqprime.ne_one hq1).elim
          · exact hqp'
        simp [this]
      · -- `q ∣ m` ⇒ `minFac m ≤ q` e, de `isRoughGE p m`, `p ≤ minFac m`
        have hq_ge_min : Nat.minFac m ≤ q :=
          minFac_le_of_prime_dvd hqprime hqm
        exact le_trans hminm hq_ge_min
  exact le_antisymm hle hge

/-! ## Direção ida: `factorSet → classOf` -/

lemma factorSet_to_class_mem
  {y X p m : ℕ} (hp : p ∈ primesIn y X) (hm : m ∈ factorSet X p) :
  p * m ∈ classOf X y p := by
  classical
  -- dados de `p`
  rcases (mem_primesIn).1 hp with ⟨hylt, _, hpPrime⟩
  have hp2 : 2 ≤ p := hpPrime.two_le
  -- dados de `m`
  rcases (Finset.mem_filter.1 hm) with ⟨hmI, hmR⟩
  rcases Finset.mem_Icc.1 hmI with ⟨hm1, hmX⟩
  -- 1 ≤ p*m ≤ X
  have hIcc : p * m ∈ Finset.Icc 1 X := by
    -- 1 ≤ p*m
    have h1 : 1 ≤ p * m := by
      have : 1 * 1 ≤ p * m := Nat.mul_le_mul (Nat.le_trans (by decide : 1 ≤ 2) hp2) hm1
      simpa using this
    -- p*m ≤ X
    have hLe : p * m ≤ X := by
      have : p * m ≤ p * (X / p) := Nat.mul_le_mul_left _ hmX
      exact this.trans (Nat.mul_div_le X p)
    exact Finset.mem_Icc.mpr ⟨h1, hLe⟩
  -- n ≠ 1
  have hne1 : p * m ≠ 1 := by
    intro h; have : (2 : ℕ) ≤ 1 := by
      have : 2 * 1 ≤ p * m := Nat.mul_le_mul hp2 hm1
      simp [h] at this
    exact (Nat.not_succ_le_self 1) this
  -- áspero(>y) e minFac
  have hmin : Nat.minFac (p * m) = p := minFac_mul_of_geRough hpPrime hmR
  have hrough : isRoughGT y (p * m) := by
    refine Or.inr ⟨?h2, ?hygt⟩
    · have : 2 * 1 ≤ p * m := Nat.mul_le_mul hp2 hm1; simpa using this
    · simpa [hmin] using hylt
  -- fecha o filtro
  exact Finset.mem_filter.2 ⟨hIcc, ⟨hne1, hrough, hmin⟩⟩

/-! ## Direção volta: `classOf → factorSet` -/

lemma class_to_factorSet_mem
  {y X p n : ℕ} (hp : p ∈ primesIn y X) (hn : n ∈ classOf X y p) :
  n / p ∈ factorSet X p := by
  classical
  -- dados de `p`
  rcases (mem_primesIn).1 hp with ⟨_, _, hpPrime⟩
  have hp_pos : 0 < p := hpPrime.pos
  -- dados de `n`
  rcases (Finset.mem_filter.1 hn) with ⟨hnI, hcond⟩
  rcases hcond with ⟨hne1, hrough, hmin⟩
  rcases Finset.mem_Icc.1 hnI with ⟨hn1, hnX⟩
  -- p ∣ n e n = p*m
  have hdiv : p ∣ n := by simpa [hmin] using Nat.minFac_dvd n
  rcases hdiv with ⟨m, hm⟩
  -- 1 ≤ m e m ≤ X/p
  have hm1 : 1 ≤ m := by
    have hm0 : m ≠ 0 := by
      intro h
      have : n = 0 := by simpa [h] using hm
      subst this
      exact (Nat.not_succ_le_self 0) hn1
    exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hm0)
  have hmX : m ≤ X / p := by
    have : p * m ≤ X := by simpa [hm] using hnX
    exact (Nat.le_div_iff_mul_le hp_pos).2 (by simpa [Nat.mul_comm] using this)
  -- áspero(≥p) para m
  have hmR : isRoughGE p m := by
    by_cases h1m : m = 1
    · exact Or.inl h1m
    · right
      have hm2 : 2 ≤ m := Nat.succ_le_of_lt (lt_of_le_of_ne hm1 (ne_comm.mp h1m))
      -- minFac m é primo e divide m; logo divide n ⇒ minFac n ≤ minFac m
      have hmin_le : Nat.minFac n ≤ Nat.minFac m := by
        have : Nat.minFac m ∣ n := by
          have : Nat.minFac m ∣ m := Nat.minFac_dvd m
          have hmd : m ∣ n := by
            rw [hm, Nat.mul_comm]
            exact dvd_mul_right m p
          exact dvd_trans this hmd
        exact minFac_le_of_prime_dvd (minFac_prime_of_two_le hm2) this
      -- de minFac n = p, conclui p ≤ minFac m
      have : p ≤ Nat.minFac m := by simpa [hmin] using hmin_le
      exact ⟨hm2, this⟩
  -- fechar filtro: reescreve `n/p = m` pela divisibilidade
  have hnp : n / p = m := by
    have : m * p / p = m := Nat.mul_div_cancel _ hp_pos
    simpa [hm, Nat.mul_comm] using this
  have hf : m ∈ factorSet X p :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hm1, hmX⟩, hmR⟩
  simpa [hnp] using hf

/-- Igualdade de cardinalidades entre `factorSet` e `classOf` via a bijeção `m ↦ p*m`
com inversa `n ↦ n/p`. Substitui o contrato temporário. -/
theorem card_factor_class_eq
  {X y p : ℕ} (hp : p ∈ primesIn y X) :
  PhiGE (X / p) p = (classOf X y p).card := by
  classical
  -- dados do primo p (evita depender de `mem_primesIn` definido abaixo)
  have hpPrime : Nat.Prime p := by
    rcases Finset.mem_filter.1 hp with ⟨_, hpPrime⟩
    exact hpPrime
  have hp_pos : 0 < p := hpPrime.pos
  -- funções dependentes para `card_bij'`
  let i : ∀ m ∈ factorSet X p, ℕ := fun m _ => p * m
  let j : ∀ n ∈ classOf X y p, ℕ := fun n _ => n / p
  -- imagens estão nas classes correspondentes
  have hi : ∀ m hm, i m hm ∈ classOf X y p := by
    intro m hm
    simpa [i] using factorSet_to_class_mem (y:=y) (X:=X) (p:=p) hp hm
  have hj : ∀ n hn, j n hn ∈ factorSet X p := by
    intro n hn
    simpa [j] using class_to_factorSet_mem (y:=y) (X:=X) (p:=p) hp hn
  -- inversões locais: j ∘ i = id e i ∘ j = id
  have left_inv : ∀ m hm, j (i m hm) (hi m hm) = m := by
    intro m hm
    simp [i, j, hp_pos]
  have right_inv : ∀ n hn, i (j n hn) (hj n hn) = n := by
    intro n hn
    -- de `n ∈ classOf` obtemos `p ∣ n` via `minFac n = p`
    rcases (Finset.mem_filter.1 hn) with ⟨_, hcond⟩
    rcases hcond with ⟨_, _, hmin⟩
    have hdiv : p ∣ n := by simpa [hmin] using Nat.minFac_dvd n
    simp [i, j, Nat.mul_div_cancel' hdiv]
  -- conclui por bijeção de finitos
  have h :=
    Finset.card_bij' (s := factorSet X p) (t := classOf X y p)
      i j hi hj left_inv right_inv
  -- reescreve `PhiGE` como card de `factorSet`
  simpa [PhiGE, factorSet] using h

/-! ## Identidade discreta para `PhiGT` -/

lemma classOf_disjoint
  {X y p₁ p₂ : ℕ}
  (_hp₁ : p₁ ∈ primesIn y X) (_hp₂ : p₂ ∈ primesIn y X) (hne : p₁ ≠ p₂) :
  Disjoint (classOf X y p₁) (classOf X y p₂) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro n hn1 hn2
  rcases Finset.mem_filter.1 hn1 with ⟨_, hcond1⟩
  rcases hcond1 with ⟨_, _, hmin1⟩
  rcases Finset.mem_filter.1 hn2 with ⟨_, hcond2⟩
  rcases hcond2 with ⟨_, _, hmin2⟩
  have hEq : p₁ = p₂ := hmin1.symm.trans hmin2
  exact hne hEq

/-- Partição de cardinalidades: separa o caso `n = 1` dos ásperos. -/
lemma split_PhiGT_card (X y : ℕ) :
  ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)).card
    = (if 1 ≤ X then 1 else 0)
    + ((Finset.Icc 1 X).filter (fun n => n ≠ 1 ∧ isRoughGT y n)).card := by
  classical
  set S := ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)) with hS
  have hpart := Finset.filter_card_add_filter_neg_card_eq_card (s := S) (p := fun n => n = 1)
  have hB : (S.filter fun n => n ≠ 1).card
      = ((Finset.Icc 1 X).filter (fun n => n ≠ 1 ∧ isRoughGT y n)).card := by
    have : S = (Finset.Icc 1 X).filter (fun n => isRoughGT y n) := rfl
    have hSetEq :
        ((Finset.Icc 1 X).filter (fun n => isRoughGT y n ∧ n ≠ 1))
        = ((Finset.Icc 1 X).filter (fun n => n ≠ 1 ∧ isRoughGT y n)) := by
      ext n; simp [and_left_comm, and_comm, and_assoc]
    have hL : (S.filter fun n => n ≠ 1)
        = ((Finset.Icc 1 X).filter (fun n => isRoughGT y n ∧ n ≠ 1)) := by
      simp [this, Finset.filter_filter]
    simpa [hL] using congrArg Finset.card hSetEq
  have h1mem : (1 ∈ S) ↔ 1 ≤ X := by
    constructor
    · intro h
      rcases Finset.mem_filter.1 h with ⟨hI, _⟩
      rcases Finset.mem_Icc.1 hI with ⟨h1le, hleX⟩
      exact le_trans h1le hleX
    · intro hX
      exact Finset.mem_filter.2 ⟨Finset.mem_Icc.mpr ⟨le_rfl, hX⟩, Or.inl rfl⟩
  have h1card : (S.filter fun n => n = 1).card = (if 1 ≤ X then 1 else 0) := by
    by_cases hS1 : 1 ∈ S
    · have : S.filter (fun n => n = 1) = ({1} : Finset ℕ) := by
        ext n; constructor
        · intro hn
          rcases Finset.mem_filter.1 hn with ⟨hnS, hn1⟩
          exact Finset.mem_singleton.2 hn1
        · intro hn
          have hn1 : n = 1 := Finset.mem_singleton.1 hn
          subst hn1
          exact Finset.mem_filter.2 ⟨hS1, rfl⟩
      simp [h1mem.mp hS1, this]
    · have : S.filter (fun n => n = 1) = (∅ : Finset ℕ) := by
        ext n; constructor
        · intro hn
          rcases Finset.mem_filter.1 hn with ⟨hnS, hn1⟩
          have : 1 ∈ S := by simpa [hn1] using hnS
          exact (by cases hS1 this)
        · intro hn; cases hn
      have hXfalse : ¬ 1 ≤ X := by
        intro hX
        exact hS1 ((h1mem.mpr hX))
      simp [hXfalse, this]
  have := by simpa [hB, h1card] using hpart.symm
  simp [hS] at this
  exact this

/-- Identidade discreta de Buchstab na forma de `PhiGT`. -/
theorem buchstab_identity_PhiGT (X y : ℕ) :
  PhiGT X y = (if 1 ≤ X then 1 else 0)
    + (Finset.sum (primesIn y X) (fun p => PhiGE (X / p) p)) := by
  classical
  -- separa o termo `n=1`
  have hsplit := split_PhiGT_card X y
  -- card do lado esquerdo é `PhiGT`
  have hPhi : PhiGT X y
      = ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)).card := rfl
  -- define base `B`
  set B := ((Finset.Icc 1 X).filter (fun n => n ≠ 1 ∧ isRoughGT y n)) with hB
  -- cardinalidade separada
  have hcard_split :
      ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)).card
        = (if 1 ≤ X then 1 else 0) + B.card := by
    simpa [hB] using hsplit
  -- transforma `B.card` em soma sobre `classOf`
  have hcover₁ :
      B ⊆ Finset.disjiUnion (primesIn y X)
              (fun p => classOf X y p)
              (by
                intro a ha b hb hneq
                exact classOf_disjoint ha hb hneq) := by
    intro n hnB
    rcases Finset.mem_filter.1 hnB with ⟨hnI, hcond⟩
    rcases hcond with ⟨hne1, hR⟩
    rcases Finset.mem_Icc.1 hnI with ⟨hn1, hnX⟩
    -- dados para `minFac n`
    have h2 : 2 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hn1 hne1.symm)
    have hylt : y < Nat.minFac n := by
      rcases hR with h1 | ⟨_, hgt⟩
      · exact (hne1 h1).elim
      · exact hgt
    have hprime : Nat.Prime (Nat.minFac n) := minFac_prime_of_two_le h2
    have hpm_leX : Nat.minFac n ≤ X := by
      have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) h2
      have hminle : Nat.minFac n ≤ n := Nat.minFac_le hpos
      exact hminle.trans hnX
    have hp_mem : Nat.minFac n ∈ primesIn y X := by
      exact (mem_primesIn).2 ⟨hylt, hpm_leX, hprime⟩
    have hmemClass : n ∈ classOf X y (Nat.minFac n) := by
      exact Finset.mem_filter.2 ⟨hnI, ⟨hne1, hR, rfl⟩⟩
    exact Finset.mem_disjiUnion.mpr ⟨Nat.minFac n, hp_mem, hmemClass⟩
  have hcover₂ :
      (Finset.disjiUnion (primesIn y X)
          (fun p => classOf X y p)
          (by intro a ha b hb hneq; exact classOf_disjoint ha hb hneq)) ⊆ B := by
    intro n hn
    rcases Finset.mem_disjiUnion.1 hn with ⟨p, hp, hnC⟩
    rcases Finset.mem_filter.1 hnC with ⟨hnI, hcond⟩
    rcases hcond with ⟨hne1, hR, hmin⟩
    exact Finset.mem_filter.2 ⟨hnI, ⟨hne1, hR⟩⟩
  have hB_eq_union :
      B = Finset.disjiUnion (primesIn y X)
            (fun p => classOf X y p)
            (by intro a ha b hb hneq; exact classOf_disjoint ha hb hneq) :=
    Finset.Subset.antisymm hcover₁ hcover₂
  have hB_card : B.card
      = Finset.sum (primesIn y X) (fun p => (classOf X y p).card) := by
    simpa [hB_eq_union] using
      (Finset.card_biUnion (s := primesIn y X) (M := ℕ) (t := fun p => classOf X y p)
        (by intro a ha b hb hneq; exact classOf_disjoint ha hb hneq))
  -- converte `classOf` em `PhiGE` usando o contrato temporário
  -- usando o contrato temporário
  have hsum : Finset.sum (primesIn y X) (fun p => PhiGE (X / p) p)
      = Finset.sum (primesIn y X) (fun p => (classOf X y p).card) := by
    refine Finset.sum_congr rfl ?h
    intro p hp
    simpa using (card_factor_class_eq (X:=X) (y:=y) (p:=p) hp)
  -- junta tudo
  have : ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)).card
      = (if 1 ≤ X then 1 else 0) + (Finset.sum (primesIn y X) (fun p => PhiGE (X / p) p)) := by
    -- replace B.card by the sum of classOf cardinals, then replace that sum by the PhiGE sum
    have h_step1 : (if 1 ≤ X then 1 else 0) + B.card
        = (if 1 ≤ X then 1 else 0) + Finset.sum (primesIn y X) (fun p => (classOf X y p).card) :=
      congrArg (fun n => (if 1 ≤ X then 1 else 0) + n) hB_card
    have h_step2 : (if 1 ≤ X then 1 else 0) + Finset.sum (primesIn y X) (fun p => (classOf X y p).card)
        = (if 1 ≤ X then 1 else 0) + Finset.sum (primesIn y X) (fun p => PhiGE (X / p) p) :=
      by
        -- hsum : Finset.sum (primesIn y X) (fun p => PhiGE (X / p) p)
        --      = Finset.sum (primesIn y X) (fun p => (classOf X y p).card)
        -- so we use the symmetric form to rewrite
        simp [Eq.symm hsum]
    calc
      ((Finset.Icc 1 X).filter (fun n => isRoughGT y n)).card = (if 1 ≤ X then 1 else 0) + B.card := hcard_split
      _ = (if 1 ≤ X then 1 else 0) + Finset.sum (primesIn y X) (fun p => PhiGE (X / p) p) := by
        rw [h_step1, h_step2]
  simpa [hPhi] using this

/-!
## Versão na janela

Na janela `(X, X+Y]`, as bijeções e contagens são provadas via `Finset.card_bij'`
e álgebra de intervalos `(X, X+Y]` e `((X/p), (X+Y)/p]`.
-/

/-- Classe do primo `p` **na janela** `(X, X+Y]`: números `X < n ≤ X+Y`, `n ≠ 1`,
`y`-ásperos (modo estrito) e com fator mínimo `p`. -/
def classOfWindow (X Y y p : ℕ) : Finset ℕ :=
  ((Finset.Icc (X+1) (X+Y)).filter fun n =>
     n ≠ 1 ∧ isRoughGT y n ∧ Nat.minFac n = p)

/-- Monotonicidade de `PhiGE` em `N`: se `N₁ ≤ N₂`, então `PhiGE N₁ p ≤ PhiGE N₂ p`. -/
lemma PhiGE_mono_in_X (p : ℕ) : Monotone (fun N => PhiGE N p) := by
  intro N1 N2 hN
  classical
  -- inclusão de intervalos [1..N1] ⊆ [1..N2]
  have hIcc : (Finset.Icc 1 N1) ⊆ (Finset.Icc 1 N2) := by
    intro n hn
    rcases Finset.mem_Icc.1 hn with ⟨h1, hn1⟩
    exact Finset.mem_Icc.2 ⟨h1, le_trans hn1 hN⟩
  -- inclusão após filtro pela propriedade `isRoughGE p`
  have hFilt :
      ((Finset.Icc 1 N1).filter (fun m => isRoughGE p m)) ⊆
      ((Finset.Icc 1 N2).filter (fun m => isRoughGE p m)) := by
    intro n hn
    rcases Finset.mem_filter.1 hn with ⟨hnI, hprop⟩
    exact Finset.mem_filter.2 ⟨hIcc hnI, hprop⟩
  -- passa a inclusão para cardinais
  simpa [PhiGE] using Finset.card_mono hFilt

/-- Alvos na janela: `X < m ≤ X+Y` com `m` `y`-áspero (modo estrito). -/
def windowTargets (y X Y : ℕ) : Finset ℕ :=
  ((Finset.Icc (X+1) (X+Y)).filter (fun m => isRoughGT y m))

/-- Para cada primo `p`, os `n` tais que `X/p < n ≤ (X+Y)/p` e `isRoughGE p n`. -/
def windowPairsFor (p X Y : ℕ) : Finset ℕ :=
  ((Finset.Icc (X / p + 1) ((X+Y) / p)).filter (fun n => isRoughGE p n))

/-- Família de pares `(p, n)` construída como união disjunta (`biUnion`) das imagens `n ↦ (p, n)`. -/
def windowPairs (y X Y : ℕ) : Finset (ℕ × ℕ) :=
  (primesIn y (X+Y)).biUnion (fun p =>
    (windowPairsFor p X Y).map
      ⟨(fun n => (p, n)), by intro a b h; cases h; rfl⟩ )

/-- Se `p` é primo, `y < p` e `isRoughGE p n`, então todo primo que divide `p*n` é `> y`
(ou seja, `mRough y (p*n)`). -/
lemma mRough_of_prime_mul_isRoughGE {y p n : ℕ}
  (hp : Nat.Prime p) (hy : y < p) (hn : isRoughGE p n) :
  RoughBlocks.mRough y (p * n) := by
  -- Alvo é do tipo: ∀ q, Prime q → q ∣ p*n → y < q
  intro q hqprime hq_dvd
  -- Fatoração do divisor em produto
  rcases (hqprime.dvd_mul.mp hq_dvd) with hqp | hqn
  · -- Caso 1: q ∣ p  ⇒  q = p
    rcases (Nat.dvd_prime hp).1 hqp with hq1 | hqp_eq
    · exact (hqprime.ne_one hq1).elim
    · -- q = p, então y < q
      simpa [hqp_eq] using hy
  · -- Caso 2: q ∣ n
    cases hn with
    | inl h1 =>
      -- n = 1 ⇒ q ∣ 1, impossível para q primo
      have : q ∣ 1 := by simpa [h1] using hqn
      exact (hqprime.ne_one (Nat.dvd_one.mp this)).elim
    | inr h2min =>
      rcases h2min with ⟨_hm2, hmin⟩
      -- minFac n ≤ q pois q | n e q é primo
      have hmin_le_q : Nat.minFac n ≤ q := minFac_le_of_prime_dvd hqprime hqn
      -- y < p ≤ minFac n ≤ q
      exact lt_of_lt_of_le hy (le_trans hmin hmin_le_q)

/-- Para cada `p`, a diferença `PhiGE ((X+Y)/p) p - PhiGE (X/p) p`
é exatamente o número de `n` em `Icc (X/p+1) ((X+Y)/p)` com `isRoughGE p n`. -/
lemma PhiGE_diff_windowPairsFor (X Y p : ℕ) :
  (PhiGE ((X+Y)/p) p) - (PhiGE (X/p) p)
  = (windowPairsFor p X Y).card := by
  classical
  -- Expande PhiGE como card do filtro em `Icc 1 ·`
  have hA : PhiGE ((X+Y)/p) p
      = ((Finset.Icc 1 ((X+Y)/p)).filter (fun n => isRoughGE p n)).card := by
    simp [PhiGE]
  have hB : PhiGE (X/p) p
      = ((Finset.Icc 1 (X/p)).filter (fun n => isRoughGE p n)).card := by
    simp [PhiGE]

  -- Decomposição de intervalos: [1..A] = [1..B] ∪ [B+1..A] com B≤A
  have hBA : X / p ≤ (X+Y) / p := Nat.div_le_div_right (Nat.le_add_right _ _)

  have hsplit :
    (Finset.Icc 1 ((X+Y)/p))
      = (Finset.Icc 1 (X/p)) ∪ (Finset.Icc (X/p+1) ((X+Y)/p)) := by
    ext n; constructor
    · intro hn
      rcases Finset.mem_Icc.1 hn with ⟨h1, hA'⟩
      -- ou n ≤ X/p, ou X/p < n
      by_cases hnb : n ≤ X / p
      · -- fica no primeiro bloco
        exact (Finset.mem_union).2 (Or.inl (Finset.mem_Icc.2 ⟨h1, hnb⟩))
      · -- fica no segundo bloco
        have hlt : X / p < n := lt_of_not_ge hnb
        have : X / p + 1 ≤ n := Nat.succ_le_of_lt hlt
        exact (Finset.mem_union).2 (Or.inr (Finset.mem_Icc.2 ⟨this, hA'⟩))
    · intro hn
      -- volta: se está em algum dos blocos, então está em [1..(X+Y)/p]
      rcases (Finset.mem_union).1 hn with h | h
      · rcases Finset.mem_Icc.1 h with ⟨h1, hB⟩
        exact Finset.mem_Icc.2 ⟨h1, le_trans hB hBA⟩
      · rcases Finset.mem_Icc.1 h with ⟨hleft, hright⟩
        have h1 : 1 ≤ n := le_trans (Nat.succ_le_succ (Nat.zero_le (X / p))) hleft
        exact Finset.mem_Icc.2 ⟨h1, hright⟩

  -- As duas partes são disjuntas depois do filtro (não pode ter n ≤ X/p e X/p+1 ≤ n)
  have hdisj :
    Disjoint
      ((Finset.Icc 1 (X/p)).filter (fun n => isRoughGE p n))
      ((Finset.Icc (X/p+1) ((X+Y)/p)).filter (fun n => isRoughGE p n)) := by
    refine Finset.disjoint_left.2 ?_
    intro n hn1 hn2
    rcases Finset.mem_filter.1 hn1 with ⟨hnI1, _⟩
    rcases Finset.mem_filter.1 hn2 with ⟨hnI2, _⟩
    rcases Finset.mem_Icc.1 hnI1 with ⟨_, hnB⟩
    rcases Finset.mem_Icc.1 hnI2 with ⟨hB1, _⟩
    -- temos n ≤ X/p e X/p+1 ≤ n ⇒ X/p < n, contradição
    exact (Nat.not_succ_le_self (X / p)) (le_trans hB1 hnB)

  -- Card do filtro na união = soma dos cards (disjunção)
  have hsumCards :
    ((Finset.Icc 1 ((X+Y)/p)).filter (fun n => isRoughGE p n)).card
      = ((Finset.Icc 1 (X/p)).filter (fun n => isRoughGE p n)).card
        + ((Finset.Icc (X/p+1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card := by
    simpa [hsplit, Finset.filter_union] using
      (Finset.card_union_of_disjoint
        (s := ((Finset.Icc 1 (X/p)).filter (fun n => isRoughGE p n)))
        (t := ((Finset.Icc (X/p+1) ((X+Y)/p)).filter (fun n => isRoughGE p n)))
        hdisj)

  -- De A = B + C obtemos C = A - B
  have hdiff :
    ((Finset.Icc (X/p+1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card
      = ((Finset.Icc 1 ((X+Y)/p)).filter (fun n => isRoughGE p n)).card
        - ((Finset.Icc 1 (X/p)).filter (fun n => isRoughGE p n)).card := by
    -- abrevia: A, B, C  (evita shadowing de `hA/hB` definidos acima)
    set A :=
      ((Finset.Icc 1 ((X+Y)/p)).filter (fun n => isRoughGE p n)).card with hAdef
    set B :=
      ((Finset.Icc 1 (X/p)).filter (fun n => isRoughGE p n)).card with hBdef
    set C :=
      ((Finset.Icc (X/p+1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card with hCdef


    -- de hsumCards: A = B + C   (use `simp` no fato e depois `exact`)
    have hAB1' := hsumCards
    simp [hAdef, hBdef, hCdef] at hAB1'
    have hAB1 : A = B + C := hAB1'

    -- então A - B = (B + C) - B
    have hAB2 : A - B = (B + C) - B := congrArg (fun t => t - B) hAB1

    -- e (B + C) - B = C (forma explícita, evitando implicitação de metas)
    have hBC : (B + C) - B = C := by
      rw [Nat.add_comm]
      exact Nat.add_sub_cancel C B

    -- junta
    have hAB : A - B = C := hAB2.trans hBC

    -- reescreve a meta para `C = A - B` e fecha (sem `simpa`)
    simp [hAdef, hBdef, hCdef]
    exact hAB.symm

  -- finaliza
  simp [windowPairsFor, hA, hB, hdiff]

/-- As imagens para `p₁ ≠ p₂` são disjuntas (primeira coordenada diferente). -/
lemma windowPairs_disjoint
  (y X Y : ℕ)
  {p₁} (_hp₁ : p₁ ∈ primesIn y (X+Y))
  {p₂} (_hp₂ : p₂ ∈ primesIn y (X+Y))
  (hneq : p₁ ≠ p₂) :
  Disjoint
    ((windowPairsFor p₁ X Y).map ⟨fun n => (p₁, n), by intro a b h; cases h; rfl⟩)
    ((windowPairsFor p₂ X Y).map ⟨fun n => (p₂, n), by intro a b h; cases h; rfl⟩) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro t ht₁ ht₂
  rcases Finset.mem_map.1 ht₁ with ⟨n₁, hn₁, rfl⟩
  rcases Finset.mem_map.1 ht₂ with ⟨n₂, hn₂, hpair⟩
  cases hpair
  exact hneq rfl

/-- `card (bind …) = ∑ card` para a nossa família. -/
lemma card_windowPairs_eq_sum (y X Y : ℕ) :
  (windowPairs y X Y).card
    = ∑ p ∈ primesIn y (X+Y), (windowPairsFor p X Y).card := by
  classical
  -- aplica `Finset.card_biUnion` (bind = biUnion) e depois simp para identificar `windowPairs`
  have h := Finset.card_biUnion
    (s := primesIn y (X+Y))
    (t := fun p => (windowPairsFor p X Y).map
      ⟨fun n => (p, n), by intro a b h; cases h; rfl⟩ )
    (by
      -- disjunção
      intro p hp q hq hpq
      -- especializa o lema anterior
      simpa using windowPairs_disjoint (y:=y) (X:=X) (Y:=Y) hp hq hpq)
  simpa [windowPairs] using h

/-- (Janela) Da faixa de fatores volta para a classe correspondente. -/
lemma windowPairsFor_to_classOfWindow_mem
  {X Y y p m : ℕ} (hp : p ∈ primesIn y (X+Y)) (hm : m ∈ windowPairsFor p X Y) :
  p * m ∈ classOfWindow X Y y p := by
  classical
  rcases (mem_primesIn).1 hp with ⟨hylt, _, hpPrime⟩
  have hp_pos : 0 < p := hpPrime.pos
  have hp2 : 2 ≤ p := hpPrime.two_le
  rcases Finset.mem_filter.1 hm with ⟨hmI, hmR⟩
  rcases Finset.mem_Icc.1 hmI with ⟨hmL, hmU⟩
  -- X+1 ≤ p*m (usa div_lt_iff_lt_mul)
  have hXLt : X < p * m := by
    have : X / p < m := by
      -- from X/p + 1 ≤ m we get X/p < m
      exact lt_of_lt_of_le (Nat.lt_succ_self _) hmL
    simpa [Nat.mul_comm] using (Nat.div_lt_iff_lt_mul hp_pos).1 this
  have hLow : X + 1 ≤ p * m := Nat.succ_le_of_lt hXLt
  -- p*m ≤ X+Y
  have hUp : p * m ≤ X + Y := by
    have : p * m ≤ p * ((X+Y)/p) := Nat.mul_le_mul_left _ hmU
    exact this.trans (Nat.mul_div_le (X+Y) p)
  -- 1 ≤ m
  have hm1 : 1 ≤ m := le_trans (Nat.succ_le_succ (Nat.zero_le _)) hmL
  -- n ≠ 1
  have hne1 : p * m ≠ 1 := by
    have : (2 : ℕ) ≤ p * m := by
      have : 2 * 1 ≤ p * m := Nat.mul_le_mul hp2 hm1
      simpa using this
    exact ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) this)
  -- minFac (p*m) = p e áspero estrito
  have hmin : Nat.minFac (p * m) = p := minFac_mul_of_geRough hpPrime hmR
  have hrough : isRoughGT y (p * m) := by
    refine Or.inr ⟨?h2, ?hygt⟩
    · have : 2 * 1 ≤ p * m := Nat.mul_le_mul hp2 hm1; simpa using this
    · simpa [hmin] using hylt
  -- fecha o filtro da classe na janela
  exact Finset.mem_filter.2
    ⟨Finset.mem_Icc.2 ⟨hLow, hUp⟩, ⟨hne1, hrough, hmin⟩⟩

/-- (Janela) Da classe correspondente volta para a faixa de fatores. -/
lemma classOfWindow_to_windowPairsFor_mem
  {X Y y p n : ℕ} (hp : p ∈ primesIn y (X+Y)) (hn : n ∈ classOfWindow X Y y p) :
  n / p ∈ windowPairsFor p X Y := by
  classical
  rcases (mem_primesIn).1 hp with ⟨_, _, hpPrime⟩
  have hp_pos : 0 < p := hpPrime.pos
  rcases Finset.mem_filter.1 hn with ⟨hnI, hcond⟩
  rcases hcond with ⟨hne1, hrough, hmin⟩
  rcases Finset.mem_Icc.1 hnI with ⟨hXL1, hUp⟩
  -- p ∣ n e n = p*m
  have hdiv : p ∣ n := by simpa [hmin] using Nat.minFac_dvd n
  rcases hdiv with ⟨m, hm⟩
  -- limites para m na janela
  have hmL : X / p + 1 ≤ m := by
    have hXLt : X < n := Nat.lt_of_succ_le hXL1
    -- X < p*m
    have hXLt' : X < p * m := by simpa [hm] using hXLt
    -- X/p < m (use commutativity of multiplication to match the expected form)
    have : X / p < m := (Nat.div_lt_iff_lt_mul hp_pos).mpr (by simpa [Nat.mul_comm] using hXLt')
    exact Nat.succ_le_of_lt this
  have hmU : m ≤ (X+Y)/p := by
    have : p * m ≤ X + Y := by simpa [hm] using hUp
    exact (Nat.le_div_iff_mul_le hp_pos).mpr (by simpa [Nat.mul_comm] using this)
  -- áspero(≥p) para m (igual ao caso global)
  have hmR : isRoughGE p m := by
    by_cases h1m : m = 1
    · exact Or.inl h1m
    · right
      -- from the left bound X / p + 1 ≤ m we get 1 ≤ m, and combined with m ≠ 1 gives 2 ≤ m
      have hm_ge1 : 1 ≤ m := by
        have : 1 ≤ X / p + 1 := Nat.succ_le_succ (Nat.zero_le _)
        exact le_trans this hmL
      have hm2 : 2 ≤ m := by
        exact Nat.succ_le_of_lt (lt_of_le_of_ne hm_ge1 (ne_comm.mp h1m))
      have hmin_le : Nat.minFac n ≤ Nat.minFac m := by
        have : Nat.minFac m ∣ n := by
          have : Nat.minFac m ∣ m := Nat.minFac_dvd m
          have hmd : m ∣ n := by
            rw [hm, Nat.mul_comm]
            exact dvd_mul_right m p
          exact dvd_trans this hmd
        exact minFac_le_of_prime_dvd (minFac_prime_of_two_le hm2) this
      have : p ≤ Nat.minFac m := by simpa [hmin] using hmin_le
      exact ⟨hm2, this⟩
  -- conclui
  have hnp : n / p = m := by
    have : m * p / p = m := Nat.mul_div_cancel _ hp_pos
    simpa [hm, Nat.mul_comm] using this
  have : m ∈ windowPairsFor p X Y :=
    Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hmL, hmU⟩, hmR⟩
  simpa [hnp] using this

/-- (Janela) Bijeção entre `windowPairsFor p` e `classOfWindow` via `m ↦ p*m` / `n ↦ n/p`. -/
lemma card_classOfWindow_eq_windowPairsFor
  {X Y y p : ℕ} (hp : p ∈ primesIn y (X+Y)) :
  (classOfWindow X Y y p).card = (windowPairsFor p X Y).card := by
  classical
  rcases (mem_primesIn).1 hp with ⟨_, _, hpPrime⟩
  have hp_pos : 0 < p := hpPrime.pos
  let i : ∀ m ∈ windowPairsFor p X Y, ℕ := fun m _ => p * m
  let j : ∀ n ∈ classOfWindow X Y y p, ℕ := fun n _ => n / p
  have hi : ∀ m hm, i m hm ∈ classOfWindow X Y y p := by
    intro m hm; simpa [i] using windowPairsFor_to_classOfWindow_mem (X:=X) (Y:=Y) (y:=y) (p:=p) hp hm
  have hj : ∀ n hn, j n hn ∈ windowPairsFor p X Y := by
    intro n hn; simpa [j] using classOfWindow_to_windowPairsFor_mem (X:=X) (Y:=Y) (y:=y) (p:=p) hp hn
  have left_inv : ∀ m hm, j (i m hm) (hi m hm) = m := by
    intro m hm; simp [i, j, hp_pos]
  have right_inv : ∀ n hn, i (j n hn) (hj n hn) = n := by
    intro n hn
    rcases (Finset.mem_filter.1 hn) with ⟨_, ⟨_, _, hmin⟩⟩
    have hdiv : p ∣ n := by simpa [hmin] using Nat.minFac_dvd n
    simp [i, j, Nat.mul_div_cancel' hdiv]
  have h := Finset.card_bij' (s := windowPairsFor p X Y) (t := classOfWindow X Y y p)
              i j hi hj left_inv right_inv
  simpa using h.symm

/-- (Janela) Disjunção entre classes de primos distintos. -/
lemma classOfWindow_disjoint
  {X Y y p₁ p₂ : ℕ}
  (_hp₁ : p₁ ∈ primesIn y (X+Y)) (_hp₂ : p₂ ∈ primesIn y (X+Y)) (hne : p₁ ≠ p₂) :
  Disjoint (classOfWindow X Y y p₁) (classOfWindow X Y y p₂) := by
  classical
  refine Finset.disjoint_left.2 ?_
  intro n hn₁ hn₂
  rcases Finset.mem_filter.1 hn₁ with ⟨_, ⟨_, _, hmin₁⟩⟩
  rcases Finset.mem_filter.1 hn₂ with ⟨_, ⟨_, _, hmin₂⟩⟩
  exact hne (hmin₁.symm.trans hmin₂)

-- (Janela) União disjunta das classes cobre exatamente os ásperos (sem `n=1`) na janela. -/
lemma cover_window_without_one (X Y y : ℕ) :
  ((Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ isRoughGT y n))
  = Finset.disjiUnion (primesIn y (X+Y)) (fun p => classOfWindow X Y y p)
      (by intro a ha b hb hneq; exact classOfWindow_disjoint ha hb hneq) := by
  classical
  -- ⊆
  refine Finset.Subset.antisymm ?lhs ?rhs
  · intro n hn
    rcases Finset.mem_filter.1 hn with ⟨hnI, ⟨hne1, hR⟩⟩
    rcases Finset.mem_Icc.1 hnI with ⟨hlow, hnUp⟩
    -- info do minFac
    have h2 : 2 ≤ n := by
      -- from hlow : X + 1 ≤ n we get 1 ≤ n, and with n ≠ 1 we obtain 2 ≤ n
      have h1 : 1 ≤ n := by
        have : 1 ≤ X + 1 := Nat.succ_le_succ (Nat.zero_le X)
        exact le_trans this hlow
      exact Nat.succ_le_of_lt (lt_of_le_of_ne h1 (ne_comm.mp hne1))
    have hylt : y < Nat.minFac n := by
      rcases hR with h1 | ⟨_, hgt⟩
      · exact (hne1 h1).elim
      · exact hgt
    have hprime : Nat.Prime (Nat.minFac n) := minFac_prime_of_two_le h2
    have hpm_le : Nat.minFac n ≤ X+Y := (Nat.minFac_le (lt_of_lt_of_le (by decide : 0 < 2) h2)).trans hnUp
    have hp_mem : Nat.minFac n ∈ primesIn y (X+Y) := (mem_primesIn).2 ⟨hylt, hpm_le, hprime⟩
    have hmemClass : n ∈ classOfWindow X Y y (Nat.minFac n) :=
      Finset.mem_filter.2 ⟨hnI, ⟨hne1, hR, rfl⟩⟩
    exact Finset.mem_disjiUnion.mpr ⟨_, hp_mem, hmemClass⟩
  · intro n hn
    rcases Finset.mem_disjiUnion.1 hn with ⟨p, hp, hnC⟩
    rcases Finset.mem_filter.1 hnC with ⟨hnI, ⟨hne1, hR, _⟩⟩
    exact Finset.mem_filter.2 ⟨hnI, ⟨hne1, hR⟩⟩

/-- (Janela) Igualdade principal (versão em ℕ, sem axiomas). -/
theorem buchstab_identity_window_core (y X Y : ℕ) :
  ((Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ isRoughGT y n)).card
    = ∑ p ∈ primesIn y (X+Y), (PhiGE ((X+Y)/p) p - PhiGE (X/p) p) := by
  classical
  -- cobre a janela por classes disjuntas
  have hcover := congrArg Finset.card (cover_window_without_one X Y y)
  -- transforma em soma de cards
  have hsum_classes :
      ((Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ isRoughGT y n)).card
      = ∑ p ∈ primesIn y (X+Y), (classOfWindow X Y y p).card := by
    simpa [Finset.disjiUnion, Finset.card_biUnion] using hcover
  -- cada classe ↔ `windowPairsFor` ↔ diferença de `PhiGE`
  have hsum_pairs :
      ∑ p ∈ primesIn y (X+Y), (classOfWindow X Y y p).card
      = ∑ p ∈ primesIn y (X+Y), (windowPairsFor p X Y).card := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    simpa using (card_classOfWindow_eq_windowPairsFor (X:=X) (Y:=Y) (y:=y) (p:=p) hp)
  have hsum_diff :
      ∑ p ∈ primesIn y (X+Y), (windowPairsFor p X Y).card
      = ∑ p ∈ primesIn y (X+Y), (PhiGE ((X+Y)/p) p - PhiGE (X/p) p) := by
    refine Finset.sum_congr rfl ?_
    intro p hp; simpa using (PhiGE_diff_windowPairsFor (X:=X) (Y:=Y) (p:=p)).symm
  -- junta
  simpa [hsum_pairs, hsum_diff] using hsum_classes

/-- Em números `n ≥ 1`, `mRough` coincide com `isRoughGT`. -/
lemma mRough_iff_not_one_isRoughGT {y n : ℕ} (hn : 1 ≤ n) :
  mRough y n ↔ isRoughGT y n := by
  classical
  constructor
  · -- (→) mRough → isRoughGT
    intro h
    by_cases h1 : n = 1
    · -- caso `n=1`
      exact Or.inl h1
    · -- caso `n ≠ 1`
      have hprime : Nat.Prime (Nat.minFac n) := Nat.minFac_prime h1
      have hdiv   : Nat.minFac n ∣ n := Nat.minFac_dvd n
      have hylt   : y < Nat.minFac n := h _ hprime hdiv
      have hn2    : 2 ≤ n := by
        have : 1 < n := lt_of_le_of_ne hn (ne_comm.mp h1)
        exact Nat.succ_le_of_lt this
      exact Or.inr ⟨hn2, hylt⟩
  · -- (←) isRoughGT → mRough
    intro h q hqprime hq_dvd
    cases h with
    | inl h1 =>
        -- impossível um primo dividir 1
        have : ¬ q ∣ 1 := hqprime.not_dvd_one
        exact (this (by simpa [h1] using hq_dvd)).elim
    | inr h2 =>
        rcases h2 with ⟨_, hymin⟩
        have hmin_le_q : Nat.minFac n ≤ q :=
          minFac_le_of_prime_dvd hqprime hq_dvd
        exact lt_of_lt_of_le hymin hmin_le_q

noncomputable instance decidable_mRough_pred (y : ℕ) : DecidablePred (fun n => mRough y n) := fun n =>
  Classical.dec (mRough y n)

theorem buchstab_identity_window (y X Y : ℕ) :
  ((Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ mRough y n)).card
    = ∑ p ∈ primesIn y (X+Y), (PhiGE ((X+Y)/p) p - PhiGE (X/p) p) := by
  classical
  -- show the filter using mRough on the window equals the filter using isRoughGT,
  -- both restricted to exclude n = 1 (this matches the core identity which excludes 1).
  have hfilter :
    (Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ mRough y n)
      = (Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ isRoughGT y n) := by
    apply Finset.filter_congr
    intro n hn
    -- from n ∈ Icc (X+1) (X+Y) we get 1 ≤ n, so we can apply the equivalence lemma
    have h1 : 1 ≤ n := by
      rcases Finset.mem_Icc.1 hn with ⟨hleft, _⟩
      exact le_trans (Nat.succ_le_succ (Nat.zero_le X)) hleft
    constructor
    · intro h; rcases h with ⟨hne1, hm⟩; exact ⟨hne1, (mRough_iff_not_one_isRoughGT h1).1 hm⟩
    · intro h; rcases h with ⟨hne1, his⟩; exact ⟨hne1, (mRough_iff_not_one_isRoughGT h1).2 his⟩
  -- take cards and combine with the core identity which is stated for the "isRoughGT" filter
  have hcard := congrArg Finset.card hfilter
  have hsum := buchstab_identity_window_core y X Y
  -- combine the equalities: card(mRough, excluding 1) = card(isRoughGT, excluding 1) = sum
  exact (hcard.trans hsum)

/-- (Janela) Igualdade do auxiliar: card da classe = diferença de `PhiGE` (sem axiomas). -/
theorem card_classOfWindow_eq
  {X Y y p : ℕ} (hp : p ∈ primesIn y (X+Y)) :
  (classOfWindow X Y y p).card
    = (PhiGE ((X+Y)/p) p - PhiGE (X/p) p) := by
  -- pela bijeção com `windowPairsFor` + `PhiGE_diff_windowPairsFor`
  have h₁ := card_classOfWindow_eq_windowPairsFor (X:=X) (Y:=Y) (y:=y) (p:=p) hp
  simpa [h₁] using (PhiGE_diff_windowPairsFor (X:=X) (Y:=Y) (p:=p)).symm

/- Identidade de Buchstab na janela **já em ℝ** (forma soma-de-diferenças).
    Prova: partimos da versão em `ℕ` (`buchstab_identity_window` provada acima),
    coerção para `ℝ` e reescrita termo a termo usando `Nat.cast_sub` e a
    monotonicidade de `PhiGE` no primeiro argumento. -/
theorem countWindow_as_sumDiff_real (y X Y : ℕ) :
  (((Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ mRough y n)).card : ℝ)
    = ∑ p ∈ primesIn y (X+Y),
      ((PhiGE ((X+Y)/p) p : ℝ) - (PhiGE (X/p) p : ℝ)) := by
  classical
  -- Partimos da versão em `ℕ` (teorema `buchstab_identity_window` provado acima)
  have hNat := buchstab_identity_window (y := y) (X := X) (Y := Y)
  -- Coerção da igualdade inteira para `ℝ` e empurra o `Nat.cast` para dentro da soma
  have hCast :
      (((Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ mRough y n)).card : ℝ)
        = (∑ p ∈ primesIn y (X+Y), (PhiGE ((X+Y)/p) p - PhiGE (X/p) p : ℕ) : ℝ) := by
    simpa [Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℝ)) hNat
  -- Converte cada parcela `((a-b) : ℕ)` para `(a : ℝ) - (b : ℝ)` usando monotonicidade
  have hRew :
      (∑ p ∈ primesIn y (X+Y), (PhiGE ((X+Y)/p) p - PhiGE (X/p) p : ℕ) : ℝ)
        = ∑ p ∈ primesIn y (X+Y),
            ((PhiGE ((X+Y)/p) p : ℝ) - (PhiGE (X/p) p : ℝ)) := by
    refine Finset.sum_congr rfl ?_;
    intro p hp
    -- `X ≤ X+Y` dá `(X / p) ≤ ((X+Y) / p)`
    have hdiv : X / p ≤ (X + Y) / p := Nat.div_le_div_right (Nat.le_add_right _ _)
    -- monotonicidade de `PhiGE` em `N`
    have hmono : PhiGE (X / p) p ≤ PhiGE ((X + Y) / p) p :=
      (PhiGE_mono_in_X p) hdiv
    -- agora convertemos o `Nat.cast` de uma diferença em `ℝ`
    simp [Nat.cast_sub hmono]  -- fecha o objetivo pontual
  -- junta as duas reescritas
  simpa [hRew] using hCast

/-- Versão em ℕ sem excluir `1` na janela, válida se `1 ≤ X`. -/
theorem buchstab_identity_window_of_posX
  (y X Y : ℕ) (hX : 1 ≤ X) :
  countWindow y X Y
    = ∑ p ∈ primesIn y (X+Y),
        (PhiGE ((X+Y)/p) p - PhiGE (X/p) p) := by
  classical
  -- Em (X, X+Y] com 1 ≤ X, todo n ≥ 2, então `n ≠ 1` é tautológico
  have hfilter :
    ((Finset.Icc (X+1) (X+Y)).filter (fun n => mRough y n))
      = ((Finset.Icc (X+1) (X+Y)).filter (fun n => n ≠ 1 ∧ mRough y n)) := by
    apply Finset.filter_congr; intro n hn; rcases Finset.mem_Icc.1 hn with ⟨hL, _⟩

    -- from X+1 ≤ n and 1 ≤ X we get 2 ≤ n, so n ≠ 1, hence the predicates are equivalent on this interval
    have two_le_n : 2 ≤ n := (Nat.succ_le_succ hX).trans hL
    constructor
    · intro hm; exact ⟨ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) two_le_n), hm⟩
    · intro h; exact h.2

  -- Substitui pela identidade “core” (que exclui 1) já provada
  have := buchstab_identity_window (y := y) (X := X) (Y := Y)
  simpa [countWindow, hfilter] using this

/-- Versão em `ℝ` alinhada ao LaTeX com `1 ≤ X`. -/
theorem countWindow_as_sumDiff_real_of_posX
  (y X Y : ℕ) (hX : 1 ≤ X) :
  lowerBoundCount y X Y =
    ∑ p ∈ primesIn y (X+Y),
      ((PhiGE ((X+Y)/p) p : ℝ) - (PhiGE (X/p) p : ℝ)) := by
  classical
  have hNat := buchstab_identity_window_of_posX y X Y hX
  -- monotonicidade para `Nat.cast_sub`
  have hdiv (p : ℕ) : X / p ≤ (X+Y) / p :=
    Nat.div_le_div_right (Nat.le_add_right _ _)
  have hmono (p : ℕ) :
      PhiGE (X / p) p ≤ PhiGE ((X+Y) / p) p :=
    (PhiGE_mono_in_X p) (hdiv p)
  calc
    lowerBoundCount y X Y
        = (countWindow y X Y : ℝ) := by simp [lowerBoundCount]
    _ = ((∑ p ∈ primesIn y (X+Y),
            (PhiGE ((X+Y)/p) p - PhiGE (X/p) p : ℕ)) : ℝ) := by
          simpa [Nat.cast_sum] using congrArg (fun n : ℕ => (n : ℝ)) hNat
    _ = ∑ p ∈ primesIn y (X+Y),
          ((PhiGE ((X+Y)/p) p : ℝ) - (PhiGE (X/p) p : ℝ)) := by
          refine Finset.sum_congr rfl ?_
          intro p hp; simp [Nat.cast_sub (hmono p)]

/-- Para `n ≥ 2`, `isRoughGT m n` é equivalente a `isRoughGE (m+1) n`. -/
lemma isRoughGT_iff_isRoughGE_succ_of_two_le {m n : ℕ} (hn2 : 2 ≤ n) :
  isRoughGT m n ↔ isRoughGE (m+1) n := by
  classical
  constructor
  · -- →
    intro h
    rcases h with rfl | ⟨hn2', hmin⟩
    · -- impossível com `n = 1` e `hn2 : 2 ≤ n`
      exfalso; exact Nat.not_succ_le_self 1 hn2
    · -- minFac n > m ⇒ minFac n ≥ m+1
      exact Or.inr ⟨hn2', Nat.succ_le_of_lt hmin⟩
  · -- ←
    intro h
    rcases h with rfl | ⟨hn2', hmin⟩
    · -- impossível com `n = 1` e `hn2 : 2 ≤ n`
      exfalso; exact Nat.not_succ_le_self 1 hn2
    · -- minFac n ≥ m+1 ⇒ minFac n > m
      exact Or.inr ⟨hn2', lt_of_lt_of_le (Nat.lt_succ_self m) hmin⟩

end RoughBlocks.Heavy
