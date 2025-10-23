/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Buchstab.Core

/-!
# WindowLink/Core — lemas de janela para `Φ_GE`

Trabalhamos a partir da definição em `Buchstab/Core.lean`:

* `PhiGE X y := ((Finset.Icc 1 X).filter (fun n => isRoughGE y n)).card`.

Conteúdo:
* `PhiGE_mono_X_WL` — monotonicidade em `X` (local a este arquivo);
* `PhiGE_diff_window_eq` — identidade exata: janela = diferença telescópica;
* `PhiGE_diff_window_ge` — desigualdade (corolário trivial da identidade);
* `PhiGE_diff_window_ge_div` — caso com divisões por `p`;
* `PhiGE_optimized`, `PhiGE_diff`, `PhiGE_diff_eq_optimized`;
* `sum_card_eq_sum_diff_phiGE` — igualdade parcela-a-parcela sob somatório (coerção `ℕ → ℝ`).
-/

namespace RoughBlocks.Heavy
open Finset
open scoped BigOperators

/-- **Identidade exata em janelas.**
Para `N₁ ≤ N₂`,
`card ((N₁, N₂] ∩ {n | isRoughGE p n}) = PhiGE N₂ p - PhiGE N₁ p`.

Prova-ideia: particionar `Icc 1 N₂` como união disjunta de `Icc 1 N₁` com
`Icc (N₁+1) N₂` e aplicar aditividade de `card`. -/
lemma PhiGE_diff_window_eq
  (p N1 N2 : ℕ) (hN : N1 ≤ N2) :
  ((Icc (N1+1) N2).filter (fun n => isRoughGE p n)).card
    = PhiGE N2 p - PhiGE N1 p := by
  classical
  let P : ℕ → Prop := fun n => isRoughGE p n
  -- Disjunção entre [1..N1] e (N1..N2].
  have h_disj :
      Disjoint ((Icc (1 : ℕ) N1).filter (fun n => P n))
               ((Icc (N1+1) N2).filter (fun n => P n)) := by
    refine disjoint_left.mpr ?_
    intro n hn₁ hn₂
    rcases mem_filter.1 hn₁ with ⟨hnI₁, _⟩
    rcases mem_Icc.1 hnI₁ with ⟨_, hN1⟩
    rcases mem_filter.1 hn₂ with ⟨hnI₂, _⟩
    rcases mem_Icc.1 hnI₂ with ⟨hN1s, _⟩
    have : N1 + 1 ≤ N1 := le_trans hN1s hN1
    exact (Nat.not_succ_le_self N1) this
  -- Cobertura: [1..N2] = [1..N1] ∪ (N1..N2].
  have h_cover :
      ((Icc (1 : ℕ) N2).filter (fun n => P n))
        =
      ((Icc (1 : ℕ) N1).filter (fun n => P n))
        ∪
      ((Icc (N1+1) N2).filter (fun n => P n)) := by
    ext n; constructor
    · intro hn
      rcases mem_filter.1 hn with ⟨hnI, hPn⟩
      rcases mem_Icc.1 hnI with ⟨h1, hN2'⟩
      by_cases hcase : n ≤ N1
      · exact mem_union.mpr <|
          Or.inl <| mem_filter.2 ⟨mem_Icc.2 ⟨h1, hcase⟩, hPn⟩
      ·
        -- De ¬(n ≤ N1) obtemos N1 < n ⇒ N1+1 ≤ n.
        have hN1le : N1 ≤ n := by
          rcases le_total N1 n with h|h
          · exact h
          · exact (False.elim (hcase h))
        have hne : N1 ≠ n := by
          intro h
          cases h
          exact hcase le_rfl
        have hN1s : N1 + 1 ≤ n := Nat.succ_le_of_lt (lt_of_le_of_ne hN1le hne)
        exact mem_union.mpr <|
          Or.inr <| mem_filter.2 ⟨mem_Icc.2 ⟨hN1s, hN2'⟩, hPn⟩
    · intro hn
      rcases mem_union.mp hn with hn | hn
      · rcases mem_filter.1 hn with ⟨hnI, hPn⟩
        rcases mem_Icc.1 hnI with ⟨h1, hN1'⟩
        have hN2' : n ≤ N2 := le_trans hN1' hN
        exact mem_filter.2 ⟨mem_Icc.2 ⟨h1, hN2'⟩, hPn⟩
      · rcases mem_filter.1 hn with ⟨hnI, hPn⟩
        rcases mem_Icc.1 hnI with ⟨hN1s, hN2'⟩
        have h1 : 1 ≤ n := le_trans (Nat.succ_le_succ (Nat.zero_le _)) hN1s
        exact mem_filter.2 ⟨mem_Icc.2 ⟨h1, hN2'⟩, hPn⟩
  -- Additividade em união disjunta.
  have h_union_card :
      ((Icc (1 : ℕ) N2).filter (fun n => P n)).card
        =
      ((Icc (1 : ℕ) N1).filter (fun n => P n)).card
        +
      ((Icc (N1+1) N2).filter (fun n => P n)).card := by
    have := card_union_add_card_inter
      (s := (Icc (1 : ℕ) N1).filter (fun n => P n))
      (t := (Icc (N1+1) N2).filter (fun n => P n))
    have hinter_empty :
      (((Icc (1 : ℕ) N1).filter (fun n => P n)) ∩
       ((Icc (N1+1) N2).filter (fun n => P n))) = (∅ : Finset ℕ) := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro n hn
      rcases Finset.mem_inter.1 hn with ⟨hn₁, hn₂⟩
      exact (Finset.disjoint_left.mp h_disj) hn₁ hn₂
    have hinter_zero :
      (((Icc (1 : ℕ) N1).filter (fun n => P n)) ∩
       ((Icc (N1+1) N2).filter (fun n => P n))).card = 0 := by
      simp [hinter_empty]
    simpa [h_cover.symm, hinter_zero, add_comm, add_left_comm, add_assoc] using this
  -- (a+b)-a = b  ⇒  card(right) = card(big) - card(left).
  have h_right_eq :
      ((Icc (N1+1) N2).filter (fun n => P n)).card
        =
      ((Icc (1 : ℕ) N2).filter (fun n => P n)).card
        - ((Icc (1 : ℕ) N1).filter (fun n => P n)).card := by
    have h := congrArg (fun t =>
      t - ((Icc (1 : ℕ) N1).filter (fun n => P n)).card) h_union_card
    simpa using h.symm
  -- Substitui por `PhiGE` e conclui.
  have hPhi :
      ((Icc (1 : ℕ) N2).filter (fun n => P n)).card
        - ((Icc (1 : ℕ) N1).filter (fun n => P n)).card
        = PhiGE N2 p - PhiGE N1 p := by
    simp [PhiGE, P]
  simpa [hPhi] using h_right_eq

/-- **Desigualdade** correspondente a `PhiGE_diff_window_eq`.
Trivial: de `a = b` deduz-se `a ≥ b`. -/
lemma PhiGE_diff_window_ge
  (p N1 N2 : ℕ) (hN : N1 ≤ N2) :
  PhiGE N2 p - PhiGE N1 p
    ≥ ((Icc (N1+1) N2).filter (fun n => isRoughGE p n)).card := by
  have h := PhiGE_diff_window_eq p N1 N2 hN
  -- `a = b` ⇒ `a ≥ b`
  simp [h]

/-- **Caso de interesse em C3**: `N₁ = X/p`, `N₂ = (X+Y)/p`.
Usa monotonicidade de `Nat.div` para obter `X/p ≤ (X+Y)/p`. -/
lemma PhiGE_diff_window_ge_div
  (p X Y : ℕ) :
  PhiGE ((X+Y)/p) p - PhiGE (X/p) p
    ≥ ((Icc (X/p + 1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card := by
  have hXY : X ≤ X + Y := Nat.le_add_right _ _
  have hdiv : X / p ≤ (X + Y) / p := Nat.div_le_div_right hXY
  simpa using PhiGE_diff_window_ge p (X / p) ((X + Y) / p) hdiv

/-- **Versão somada**. Para cada parcela (mesmo índice `p`), o cardinal da janela
coincide com a diferença correspondente de `PhiGE` após coerção `ℕ → ℝ`. -/
lemma sum_card_eq_sum_diff_phiGE
  {y X Y : ℕ} :
  ∑ p ∈ (primesIn y (X+Y)).filter (fun p => p ≤ X),
      (((Icc (X/p + 1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card : ℝ)
  =
  ∑ p ∈ (primesIn y (X+Y)).filter (fun p => p ≤ X),
      ((PhiGE ((X+Y)/p) p : ℝ) - (PhiGE (X/p) p : ℝ)) := by
  classical
  -- Igualdade parcela-a-parcela → `sum_congr`.
  refine Finset.sum_congr rfl ?hpoint
  intro p hp
  -- Monotonicidade da divisão: X/p ≤ (X+Y)/p.
  have hdiv : X / p ≤ (X + Y) / p := Nat.div_le_div_right (Nat.le_add_right _ _)
  -- Igualdade em ℕ (janela = diferença).
  have hℕ :
    ((Icc (X/p + 1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card
      = PhiGE ((X+Y)/p) p - PhiGE (X/p) p :=
    (PhiGE_diff_window_eq p (X/p) ((X+Y)/p) hdiv)
  -- Garantia para `Nat.cast_sub`.
  have hmono : PhiGE (X/p) p ≤ PhiGE ((X+Y)/p) p :=
    PhiGE_mono_X hdiv
  -- Passa para ℝ (coerção do `Nat.sub`).
  have hℝ :
    (((Icc (X/p + 1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card : ℝ)
      = (PhiGE ((X+Y)/p) p : ℝ) - (PhiGE (X/p) p : ℝ) := by
    calc
      (((Icc (X/p + 1) ((X+Y)/p)).filter (fun n => isRoughGE p n)).card : ℝ)
          = ((PhiGE ((X+Y)/p) p - PhiGE (X/p) p : ℕ) : ℝ) := by
              exact congrArg (fun n : ℕ => (n : ℝ)) hℕ
      _ = (PhiGE ((X+Y)/p) p : ℝ) - (PhiGE (X/p) p : ℝ) := by
              simpa using (Nat.cast_sub hmono)
  -- Fecha por igualdade parcela-a-parcela.
  simp [hℝ]

/-- Versão “otimizada” da janela — apenas atalho de notação. -/
def PhiGE_optimized (start stop y : ℕ) : ℕ :=
  ((Icc start stop).filter (fun n => isRoughGE y n)).card

/-- Diferença no bloco `(m^2 + x m, m^2 + (x+1)m]`. -/
def PhiGE_diff (m x : ℕ) : ℕ :=
  let start := m^2 + x * m
  let stop  := m^2 + (x + 1) * m
  PhiGE_optimized (start + 1) stop (m + 1)

/-- Igualdade “diferença = janela otimizada” para o bloco. -/
lemma PhiGE_diff_eq_optimized (m x : ℕ) :
  let start := m^2 + x * m
  let stop  := m^2 + (x + 1) * m
  (PhiGE stop (m+1) - PhiGE start (m+1)) = PhiGE_optimized (start+1) stop (m+1) := by
  classical
  intro start stop
  -- `stop = start + m` via `(x+1)*m = x*m + m`
  have hx1 : (x + 1) * m = x * m + m := by simpa [Nat.add_mul, Nat.one_mul]
  have hstop : stop = start + m := by
    dsimp [start, stop]
    calc
      m ^ 2 + (x + 1) * m
          = m ^ 2 + (x * m + m) := by simpa [hx1]
      _   = (m ^ 2 + x * m) + m := by
            simp [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
  have hle : start ≤ stop := by
    simpa [hstop] using (Nat.le_add_right start m)
  -- usa a identidade de janela e vira o lado
  have h := PhiGE_diff_window_eq (m+1) start stop hle
  simpa [PhiGE_optimized] using h.symm

end RoughBlocks.Heavy
