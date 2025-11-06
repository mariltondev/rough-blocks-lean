/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Light.Export
import RoughBlocks.Defs
import RoughBlocks.Heavy.Buchstab.Core
import RoughBlocks.Heavy.WindowLink.Core
import RoughBlocks.Heavy.Identity
import RoughBlocks.Heavy.Numeric

/-!
# RoughBlocks.Light.Concrete

Fecha o 1×1 (ramo `m ≥ 10^6`) amarrando:
- identidade de janela (contagem no bloco = diferença de Φ),
- lema local analítico (Φ-dif ≥ LB) — assumido como hipótese aqui,
- orçamento `LB ≥ 1`.

Resultado: existência de um `m`-áspero em `K m x`.
-/

namespace RoughBlocks.Light

open RoughBlocks
open RoughBlocks.Heavy
open Classical
open Finset

/-- Forma canônica do bloco como intervalo fechado (útil para `simp`). -/
lemma K_as_Icc (m x : ℕ) :
  K m x = Icc (m*m + x*m + 1) (m*m + x*m + m) := by
  dsimp [RoughBlocks.K]
  simp [pow_two]
  -- (x+1)*m = x*m + m
  have : (x + 1) * m = x * m + m := by
    simpa [Nat.succ_eq_add_one] using (Nat.succ_mul x m)
  simp [this, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]

/-- Para `n` no bloco `K m x`, vale
`mRough m n ↔ isRoughGE (m+1) n`.

É só desenrolar as definições:
`isRoughGE (m+1) n` significa `n = 1 ∨ (2 ≤ n ∧ minFac n ≥ m+1)`,
equivalente a `n = 1 ∨ (2 ≤ n ∧ minFac n > m)` (ou seja, `isRoughGT m n`);
e, para `1 ≤ n`, temos `mRough m n ↔ isRoughGT m n`. -/
lemma mRough_iff_isRoughGE_succ_on_block
  (m x n : ℕ) (hn : n ∈ K m x) :
  mRough m n ↔ isRoughGE (m+1) n := by
  -- em `K m x` temos `n ≥ m^2 + x*m + 1 ≥ 1`
  have h_low : (m*m + x*m + 1) ≤ n :=
    (mem_Icc.mp (by simpa [K_as_Icc] using hn)).1
  have hn_ge1 : 1 ≤ n := le_trans (Nat.succ_le_succ (Nat.zero_le _)) h_low
  -- `isRoughGE (m+1) n` ↔ `isRoughGT m n` por definição
  have hGE_succ_iff_GT : isRoughGE (m+1) n ↔ isRoughGT m n := by
    -- `m+1 ≤ minFac n` ↔ `m < minFac n`
    simp [isRoughGE, isRoughGT, Nat.succ_le]
  -- e `isRoughGT m n` ↔ `mRough m n` para `1 ≤ n`
  have hGT_iff_mRough : isRoughGT m n ↔ mRough m n :=
    (mRough_iff_not_one_isRoughGT (y := m) (n := n) hn_ge1).symm
  -- conclui
  exact (Iff.trans hGT_iff_mRough.symm hGE_succ_iff_GT.symm)

/-- Igualdade “contagem no bloco = diferença de Φ” já em `ℝ`.

A identidade de janela do `Core` é para o predicado `isRoughGE p`.
Aqui instanciamos com `p := m+1` e usamos que, no bloco,
`mRough m` e `isRoughGE (m+1)` são ponto-a-ponto equivalentes. -/
lemma count_block_eq_PhiDiff_real (m x : ℕ) :
  (countRoughInBlock m x : ℝ)
    = ((PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ)) := by
  classical
  set X : ℕ := m*m + x*m
  set Y : ℕ := m
  have hXY : X ≤ X + Y := Nat.le_add_right _ _
  -- igualdade em ℕ do Core, com p := m+1
  have hNat :
      (((Icc (X+1) (X+Y)).filter (fun n => isRoughGE (m+1) n)).card : ℕ)
        = PhiGE (X+Y) (m+1) - PhiGE X (m+1) :=
    RoughBlocks.Heavy.PhiGE_diff_window_eq (p := m+1) (N1 := X) (N2 := X+Y) (hN := hXY)
  -- monotonicidade para poder usar Nat.cast_sub
  have hmono : PhiGE X (m+1) ≤ PhiGE (X+Y) (m+1) :=
    (PhiGE_mono_in_X (m+1)) hXY
  -- levanta para ℝ
  have hReal :
      (((Icc (X+1) (X+Y)).filter (fun n => isRoughGE (m+1) n)).card : ℝ)
        = (PhiGE (X+Y) (m+1) : ℝ) - (PhiGE X (m+1) : ℝ) := by
    simpa [Nat.cast_sub hmono] using congrArg (fun n : ℕ => (n : ℝ)) hNat
  -- identifica a janela do bloco
  have hK : K m x = Icc (X+1) (X+Y) := by
    simp [X, Y, K_as_Icc, Nat.add_comm, Nat.add_assoc]
  -- troca o predicado do filtro via equivalência no bloco
  have hPred :
      ((K m x).filter (mRough m)) = ((K m x).filter (fun n => isRoughGE (m+1) n)) := by
    ext n; constructor <;> intro hn
    ·
      have hmrough : mRough m n := (mem_filter.mp hn).2
      have hiff :=
        mRough_iff_isRoughGE_succ_on_block m x n (by simpa [hK] using (mem_filter.mp hn).1)
      have hGE : isRoughGE (m+1) n := (Iff.mp hiff) hmrough
      exact mem_filter.mpr ⟨(mem_filter.mp hn).1, hGE⟩
    ·
      have hGE : isRoughGE (m+1) n := (mem_filter.mp hn).2
      have hiff :=
        mRough_iff_isRoughGE_succ_on_block m x n (by simpa [hK] using (mem_filter.mp hn).1)
      have hmrough : mRough m n := (Iff.mpr hiff) hGE
      exact mem_filter.mpr ⟨(mem_filter.mp hn).1, hmrough⟩
  -- conclui
  calc
    (countRoughInBlock m x : ℝ)
        = (((K m x).filter (mRough m)).card : ℝ) := by
          dsimp [RoughBlocks.countRoughInBlock, RoughBlocks.roughSetInBlock]
    _   = (((K m x).filter (fun n => isRoughGE (m+1) n)).card : ℝ) := by
          simp [hPred]
    _   = (((Icc (X+1) (X+Y)).filter (fun n => isRoughGE (m+1) n)).card : ℝ) := by
          simp [hK]
    _   = (PhiGE (X+Y) (m+1) : ℝ) - (PhiGE X (m+1) : ℝ) := hReal
    _   = (PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ) := by
          simp [X, Y, Nat.add_comm]

/-- **Corolário (ramo `m ≥ 10^6`)**.

Assume o lema local analítico na mesma janela do bloco:
`((PhiGE (m^2+x m + m) (m+1) : ℝ) - (PhiGE (m^2+x m) (m+1) : ℝ)) ≥ LB m x`. -/
theorem exist_in_block_ge_1e6
  {m x : ℕ} (hm : 1_000_000 ≤ m) (hx : x ≤ 8)
  (hPhiDiff_ge_LB :
      ((PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ)) ≥ LB m x)
  : ∃ n ∈ K m x, mRough m n := by
  -- 1) Orçamento: LB ≥ 1
  have hLB : (1 : ℝ) ≤ LB m x := (main_theorem_ge_1e6 hm hx : _)
  -- 2) Identidade de janela: contagem = Φ-dif (com p := m+1)
  have hCountEq :
      (countRoughInBlock m x : ℝ)
        = ((PhiGE (m*m + x*m + m) (m+1) : ℝ) - (PhiGE (m*m + x*m) (m+1) : ℝ)) :=
    count_block_eq_PhiDiff_real m x
  -- 3) Ponte (Heavy.Bridge): LB ≤ contagem
  have hm2 : 2 ≤ m := le_trans (by decide : (2 : ℕ) ≤ 1_000_000) hm
  have hBridge :
      (LB m x : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ) :=
    RoughBlocks.Heavy.LB_le_count_block
      (PhiGE := fun N p => (PhiGE N (p+1) : ℝ))
      m x hm2 hx
      (by simpa using hPhiDiff_ge_LB)
      (by simpa using hCountEq)
  -- 4) Conclui existência
  have hCountℝ : (1 : ℝ) ≤ (RoughBlocks.countRoughInBlock m x : ℝ) :=
    le_trans hLB hBridge
  have hCountℕ : 1 ≤ RoughBlocks.countRoughInBlock m x := by
    exact_mod_cast hCountℝ
  exact RoughBlocks.exists_of_count_ge_one hCountℕ





/--
Lema local: `Φ_GE` em janela curta `[m² + x·m, m² + (x+1)·m]`
tem um lower bound tipo Dusart–Buchstab.

Para `m ≥ 2` e `x ≤ 8`:

\[
Φ_GE(m² + x·m + m, m+1) − Φ_GE(m² + x·m, m+1)
≥ \frac{m}{\log m}·ω\!\Big(\frac{\log(m²+x·m)}{\log m}\Big)
  − C₁·\frac{m}{(\log m)²} − C₂
\]
-/
theorem local_window_lower_bound
  {m x : ℕ} (hm : 2 ≤ m) (hx : x ≤ 8)
  (hPhiGE_ge_LB :
     (Numeric.LB m x : ℝ)
       ≤ ((PhiGE (m*m + x*m + m) (m+1) : ℝ)
            - (PhiGE (m*m + x*m) (m+1) : ℝ))) :
  ((PhiGE (m*m + x*m + m) (m+1) : ℝ) -
   (PhiGE (m*m + x*m) (m+1) : ℝ))
    ≥ (m : ℝ) / Real.log m *
        Buchstab.omega
          (Real.log ((m*m + x*m : ℕ) : ℝ) / Real.log m)
      - (Numeric.C1Default : ℝ) * ((m : ℝ) / (Real.log m)^2)
      - (Numeric.C2Default : ℝ) := by
  ------------------------------------------------------------------
  -- Fase 1: propriedades básicas
  ------------------------------------------------------------------
  have hm_pos : 0 < (m : ℝ) := by
    -- de 2 ≤ m obtemos 0 < (m:ℝ)
    exact_mod_cast (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hm)
  have hlog_pos : 0 < Real.log (m : ℝ) := Numeric.log_pos_of_ge_two hm
  have hlog_ne : Real.log (m : ℝ) ≠ 0 := ne_of_gt hlog_pos

  ------------------------------------------------------------------
  -- Fase 2: define u := log(m² + x·m)/log m e prova u ≥ 1
  ------------------------------------------------------------------
  set u := Real.log ((m*m + x*m : ℕ) : ℝ) / Real.log (m : ℝ) with hu
  have hu_ge_one : 1 ≤ u := by
    -- Mostramos: log m ≤ log X, com X = m^2 + x m, e então usamos one_le_div_iff.
    have hm_gt1 : (1 : ℝ) < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by decide : (1 : ℕ) < 2) hm)
    have hX_ge_m2_nat : m*m ≤ m*m + x*m := Nat.le_add_right _ _
    have hX_ge_m2 : (m : ℝ) * (m : ℝ) ≤ ((m*m + x*m : ℕ) : ℝ) := by exact_mod_cast hX_ge_m2_nat
    have hm2_pos : 0 < (m : ℝ) * (m : ℝ) := by
      have : 0 < (m : ℝ) := lt_trans zero_lt_one hm_gt1
      simpa [pow_two] using mul_pos this this
    have hlog_m2 : Real.log ((m : ℝ) * (m : ℝ)) = (2 : ℝ) * Real.log (m : ℝ) := by
      have hmul := Real.log_mul (ne_of_gt (lt_trans zero_lt_one hm_gt1)) (ne_of_gt (lt_trans zero_lt_one hm_gt1))
      simpa [two_mul] using hmul
    have hlog_le : Real.log ((m : ℝ) * (m : ℝ)) ≤ Real.log ((m*m + x*m : ℕ) : ℝ) :=
      Real.log_le_log hm2_pos hX_ge_m2
    have hLm_nonneg : 0 ≤ Real.log (m : ℝ) := le_of_lt hlog_pos
    have hLm_le_2Lm : Real.log (m : ℝ) ≤ (2 : ℝ) * Real.log (m : ℝ) := by
      have : (1 : ℝ) ≤ 2 := by norm_num
      simpa [one_mul] using mul_le_mul_of_nonneg_right this hLm_nonneg
    have hLm_le_logX : Real.log (m : ℝ) ≤ Real.log ((m*m + x*m : ℕ) : ℝ) := by
      have : (2 : ℝ) * Real.log (m : ℝ) ≤ Real.log ((m*m + x*m : ℕ) : ℝ) := by
        simpa [hlog_m2] using hlog_le
      exact le_trans hLm_le_2Lm this
    have : 1 ≤ Real.log ((m*m + x*m : ℕ) : ℝ) / Real.log (m : ℝ) := by
      -- divide both sides of `Real.log m ≤ Real.log X` by the positive `Real.log m`
      have hinv_pos_lt : 0 < (1 / Real.log (m : ℝ)) := by
        apply div_pos
        norm_num
        exact hlog_pos
      have hinv_pos := le_of_lt hinv_pos_lt
      have one_eq : (1 : ℝ) = Real.log (m : ℝ) * (1 / Real.log (m : ℝ)) := by
        field_simp [hlog_ne]
      calc
        1 = Real.log (m : ℝ) * (1 / Real.log (m : ℝ)) := by simpa using one_eq
        _ ≤ Real.log ((m*m + x*m : ℕ) : ℝ) * (1 / Real.log (m : ℝ)) := by
          apply mul_le_mul_of_nonneg_right hLm_le_logX hinv_pos
        _ = Real.log ((m*m + x*m : ℕ) : ℝ) / Real.log (m : ℝ) := by
          simp [div_eq_mul_inv]
    simpa [u]

  ------------------------------------------------------------------
  -- Fase 3: reescreve o lower bound explícito (LB)
  ------------------------------------------------------------------
  have h_LB : (Numeric.LB m x : ℝ) =
      (m : ℝ) / Real.log m *
        Buchstab.omega u
      - (Numeric.C1Default : ℝ) * ((m : ℝ) / (Real.log m)^2)
      - (Numeric.C2Default : ℝ) := by
    simp [Numeric.LB, u, pow_two, div_eq_mul_inv,
          mul_comm, mul_left_comm, mul_assoc, Numeric.C1Default, Numeric.C2Default]

  ------------------------------------------------------------------
  -- Fase 4: aplica a desigualdade estrutural LB ≤ Φ_diff
  --
  -- Use the Heavy lemma that gives the Φ_GE window lower bound directly.
  ------------------------------------------------------------------
  have hΦ : (Numeric.LB m x : ℝ)
      ≤ ((PhiGE (m*m + x*m + m) (m+1) : ℝ)
          - (PhiGE (m*m + x*m) (m+1) : ℝ)) := by
    -- use the provided hypothesis (e.g. from the Heavy module)
    exact hPhiGE_ge_LB

  ------------------------------------------------------------------
  -- Fase 5: substitui LB pelo lado explícito
  ------------------------------------------------------------------
  simpa [h_LB] using hΦ


#print axioms RoughBlocks.Light.local_window_lower_bound
#check RoughBlocks.Light.local_window_lower_bound



end RoughBlocks.Light
