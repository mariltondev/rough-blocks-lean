/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.WindowLink.Core
import RoughBlocks.Heavy.Identity

/-!
# WindowLink/Block — ponte bloco ↔ janela (caso `p := m+1`)

Este módulo conecta a contagem discreta de números `m`-ásperos dentro do
**bloco curto** `K(m,x)` à **diferença telescópica** de `PhiGE` na janela
correspondente `(X, X+Y]`, com `X = m^2 + x·m` e `Y = m`.

A ponte ocorre em três etapas padronizadas:
1. Reescrever o bloco `K(m,x)` como uma janela `Icc (X+1) (X+Y)`.
2. Trocar o predicado de aspereza do núcleo `mRough m` por `isRoughGT m`,
   e então por `isRoughGE (m+1)` **na mesma janela**.
3. Aplicar a identidade de janela de `PhiGE` (de `WindowLink/Core`) e
   passar para `ℝ` quando necessário.

## Dependências
* `RoughBlocks.Defs` — `mRough`, `K`, `countRoughInBlock`.
* `RoughBlocks.Heavy.WindowLink.Core` — identidades de janela para `PhiGE`.
* `RoughBlocks.Heavy.Identity` — equivalências entre `mRough`, `isRoughGT`
  e `isRoughGE (m+1)`, além de monotonicidade para coerções.

## Conteúdo
* `countRoughInBlock_as_window` — forma canônica do bloco como janela.
* `window_filter_switch_GE_succ` — troca de `isRoughGT m` para `isRoughGE (m+1)` na janela.
* `strict_window_card_eq_phiDiff_succ` — card da janela = dif. de `PhiGE` (em `ℕ`).
* `strict_window_card_eq_phiDiff_succ_real` — mesma igualdade em `ℝ`.
* `countRoughInBlock_eq_phiDiff_succ_real` — **ponte final**: contagem no bloco = dif. de `PhiGE` (em `ℝ`).

> Observação: as hipóteses mínimas (por ex., `1 ≤ X` ou `2 ≤ m`) aparecem
> apenas para garantir que os lemas de equivalência entre predicados de aspereza
> sejam aplicáveis na janela em questão.
-/

namespace RoughBlocks.Heavy
open Finset

/-- Diferença `Φ` no bloco `x`, no nível `m`. -/
@[inline] def PhiDiffAt (m : ℕ) (x : ℕ) : ℝ :=
  (PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ)

/-- **Forma canônica (bloco como janela).**
Reescreve `countRoughInBlock m x` como o cardinal do filtro em
`Icc (m^2 + x·m + 1) (m^2 + x·m + m)`. Útil para `simp`/normalizações. -/
lemma countRoughInBlock_as_window (m x : ℕ) :
  RoughBlocks.countRoughInBlock m x
    = ((Finset.Icc (m^2 + x*m + 1) (m^2 + x*m + m)).filter (mRough m)).card := by
  classical
  -- `K(m,x) = Icc (m^2 + x m + 1) (m^2 + (x+1) m)` e `(x+1) m = x m + m`
  simp [countRoughInBlock, roughSetInBlock, K,
        pow_two, Nat.mul_add, add_comm, add_left_comm, add_assoc, Nat.mul_comm]

/-- **Troca de predicado na janela** `(X, X+Y]`:
`isRoughGT m` ⇔ `isRoughGE (m+1)`.

Exige `1 ≤ X` para obter `2 ≤ n` em toda a janela. -/
lemma window_filter_switch_GE_succ
  (m X Y : ℕ) (hX : 1 ≤ X) :
  ((Finset.Icc (X+1) (X+Y)).filter (fun n => isRoughGT m n))
    =
  ((Finset.Icc (X+1) (X+Y)).filter (fun n => isRoughGE (m+1) n)) := by
  classical
  apply Finset.filter_congr
  intro n hn
  -- de `X+1 ≤ n` e `1 ≤ X` obtemos `2 ≤ n`
  have hn2 : 2 ≤ n := by
    rcases Finset.mem_Icc.1 hn with ⟨hL, _⟩
    exact (Nat.succ_le_succ hX).trans hL
  simpa using (isRoughGT_iff_isRoughGE_succ_of_two_le (m := m) (n := n) hn2)

/-- **Janela ↔ diferença de `PhiGE` (ℕ)** com `p := m+1`. -/
lemma strict_window_card_eq_phiDiff_succ
  (m X Y : ℕ) (hX : 1 ≤ X) :
  ((Finset.Icc (X+1) (X+Y)).filter (fun n => isRoughGT m n)).card
    = PhiGE (X+Y) (m+1) - PhiGE X (m+1) := by
  classical
  -- troca o filtro pelo `GE (m+1)`
  have hswap := window_filter_switch_GE_succ (m := m) (X := X) (Y := Y) hX
  -- identidade de janela
  have hwin := PhiGE_diff_window_eq (p := m+1) (N1 := X) (N2 := X+Y)
                                     (hN := Nat.le_add_right _ _)
  -- basta reescrever pelo hswap (sem .symm!)
  simpa [hswap] using hwin

/-- **Janela ↔ diferença de `PhiGE` (ℝ)** com `p := m+1`.

Passo adicional: monotonicidade de `PhiGE` garante `Nat.cast_sub`. -/
lemma strict_window_card_eq_phiDiff_succ_real
  (m X Y : ℕ) (hX : 1 ≤ X) :
  (((Finset.Icc (X+1) (X+Y)).filter (fun n => isRoughGT m n)).card : ℝ)
    = ((PhiGE (X+Y) (m+1) : ℝ) - (PhiGE X (m+1) : ℝ)) := by
  classical
  -- versão em ℕ
  have hNat := strict_window_card_eq_phiDiff_succ m X Y hX
  -- monotonicidade para usar Nat.cast_sub
  have hmono : PhiGE X (m+1) ≤ PhiGE (X+Y) (m+1) :=
    (PhiGE_mono_in_X (p := m+1)) (Nat.le_add_right _ _)
  -- converte para ℝ e reescreve a diferença
  have := congrArg (fun n : ℕ => (n : ℝ)) hNat
  simpa [Nat.cast_sub hmono] using this

/-- **Ponte bloco → diferença de `PhiGE` (p := m+1), em `ℝ`.**

Hipóteses:
* `hm : 2 ≤ m` (usa-se para deduzir `1 ≤ X`);
* `_hx : x ≤ 8` (não é usado aqui; acompanha a assinatura padrão do projeto).

Ideia: (i) escrever o bloco como janela, (ii) trocar `mRough m` por `isRoughGT m`
na janela e (iii) aplicar a identidade de janela com `p = m+1`. -/
theorem countRoughInBlock_eq_phiDiff_succ_real
  (m x : ℕ) (hm : 2 ≤ m) (_hx : x ≤ 8) :
  (RoughBlocks.countRoughInBlock m x : ℝ)
    = ((PhiGE (m*m + x*m + m) (m+1) : ℝ)
        - (PhiGE (m*m + x*m) (m+1) : ℝ)) := by
  classical
  -- define a janela
  set X : ℕ := m*m + x*m
  set Y : ℕ := m

  -- de `m ≥ 2` obtemos `1 ≤ X`
  have hX : 1 ≤ X := by
    have : (1 : ℕ) ≤ m*m := by
      have : 4 ≤ m*m := by
        simpa [pow_two, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using Nat.mul_le_mul hm hm
      exact (le_trans (by decide : 1 ≤ 4) this)
    exact (le_trans this (Nat.le_add_right _ _))

  -- (1) bloco = janela com `mRough`
  have hBlock_mR :
    (RoughBlocks.countRoughInBlock m x)
      = ((Finset.Icc (X+1) (X+Y)).filter (RoughBlocks.mRough m)).card := by
    simpa [X, Y, pow_two, Nat.mul_add, add_comm, add_left_comm, add_assoc, Nat.mul_comm]
      using countRoughInBlock_as_window m x

  -- (2) troca `mRough` ↔ `isRoughGT` **na mesma janela**
  have hswap_pred :
    ((Finset.Icc (X+1) (X+Y)).filter (RoughBlocks.mRough m))
      =
    ((Finset.Icc (X+1) (X+Y)).filter (fun n => isRoughGT m n)) := by
    apply Finset.filter_congr
    intro n hn
    -- 1 ≤ n na janela
    have hn1 : 1 ≤ n := by
      rcases Finset.mem_Icc.1 hn with ⟨hL, _⟩
      exact (Nat.succ_le_succ (Nat.zero_le _)).trans hL
    -- equivalência pontual do `Identity.lean`
    simpa using (mRough_iff_not_one_isRoughGT (y := m) (n := n) hn1)

  -- (3) janela com `isRoughGT m` ↔ diferença de `PhiGE` (p = m+1)
  have H := strict_window_card_eq_phiDiff_succ_real (m := m) (X := X) (Y := Y) hX

  -- conclui
  simpa [hBlock_mR, hswap_pred, X, Y] using H

end RoughBlocks.Heavy
