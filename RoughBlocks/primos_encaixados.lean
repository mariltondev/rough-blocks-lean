/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib
import RoughBlocks.Light.B2Support

open Nat
open RoughBlocks.Light

-- Tomando como ponto de partida 'theorem existence_main_all' já valido e provado:

/-! ### Lemas aritméticos determinísticos -/
/-- `(m+1)^2` é estritamente maior que `m^2 + m`. -/
lemma block0_top_lt (m : ℕ) : m*m + m < (m+1)*(m+1) := by
  -- m < m+m+1
  have hm_le : m ≤ m + m := Nat.le_add_left _ _
  have hm_lt : m < m + m + 1 := lt_of_le_of_lt hm_le (Nat.lt_succ_self _)
  -- somar m*m dos dois lados
  have h' : m*m + m < m*m + (m + m + 1) := Nat.add_lt_add_left hm_lt (m*m)
  -- m*m + (m+m+1) = (m+1)^2
  have hEq : m*m + (m + m + 1) = (m+1)*(m+1) := by
    ring
  -- concluir
  simpa [hEq] using h'

/-- `m^2 + 2m < (m+1)^2`. -/
lemma block1_top_lt (m : ℕ) : m*m + 2*m < (m+1)*(m+1) := by
  -- m^2 + 2m < m^2 + 2m + 1
  have hstep : m*m + 2*m < m*m + 2*m + 1 := Nat.lt_succ_self _
  -- m*m + 2*m + 1 = (m+1)^2
  have hEq : m*m + 2*m + 1 = (m+1)*(m+1) := by
    ring
  -- concluir
  simpa [hEq] using hstep

/-- `m^2 < (m+1)^2`. -/
lemma sq_lt_succ_sq (m : ℕ) : m*m < (m+1)*(m+1) := by
  -- m^2 < m^2 + (2m+1)
  have hpos : 0 < 2*m + 1 := Nat.succ_pos _
  have hstep : m*m < m*m + (2*m + 1) := Nat.lt_add_of_pos_right hpos
  -- m*m + (2*m+1) = (m+1)^2
  have hEq : m*m + (2*m + 1) = (m+1)*(m+1) := by
    ring
  -- concluir
  simpa [hEq] using hstep

/-- Ponte para `m := p+1`: `(p+1)^2 + (p+1) < (p+2)^2`. -/
lemma succ_block_bridge (p : ℕ) :
  (p+1)*(p+1) + (p+1) < (p+2)*(p+2) := by
  -- (p+1) ≤ 2(p+1) ⇒ (p+1) < 2(p+1) + 1
  have hle : (p+1) ≤ 2*(p+1) := calc
    (p+1) ≤ (p+1) + (p+1) := Nat.le_add_left _ _
    _     = 2*(p+1)       := by simp [two_mul]
  have hlt : (p+1) < 2*(p+1) + 1 := lt_of_le_of_lt hle (Nat.lt_succ_self _)
  -- somar (p+1)^2 dos dois lados
  have h' :
      (p+1)*(p+1) + (p+1) < (p+1)*(p+1) + (2*(p+1) + 1) :=
    Nat.add_lt_add_left hlt ((p+1)*(p+1))
  -- (p+1)^2 + (2(p+1)+1) = (p+2)^2
  have hEq :
      (p+1)*(p+1) + (2*(p+1) + 1) = (p+2)*(p+2) := by
    ring
  -- concluir sem `simpa`
  rw [← hEq]
  exact h'

/-- Ponte genérica: se `NoSmallPrime m n` (isto é, nenhum primo `q ≤ m` divide `n`),
    então qualquer primo `q ≤ m` não divide `n`. Conveniência para reuso. -/
lemma noSmall_forbids_small_div
    {m n q : Nat}
    (hNSP : NoSmallPrime m n) (hq : Nat.Prime q) (hq_le : q ≤ m) :
    q ∣ n → False := by
  intro hqd
  exact (hNSP (q:=q) hq hq_le) hqd

/-- Se `n` é composto e `NoSmallPrime m n`, então `(m+1)^2 ≤ n`.
    Ideia: pegue `p` primo com `p ∣ n`. Pelo `NoSmallPrime`, `m < p`.
    Escreva `n = p * q` (com `q = n / p`). Como `n` não é primo, tem `q ≠ 1`,
    e como `1 < n`, tem também `q ≠ 0`; logo `2 ≤ q`. Pegue um primo `q' ∣ q`;
    então `m < q' ≤ q`. Conclui `(m+1)^2 ≤ p*q = n`. -/
lemma comp_ge_sq_of_noSmall
    {m n : Nat} (hNSP : NoSmallPrime m n)
    (hnc : ¬ Nat.Prime n) (hn1 : 1 < n) :
    (m+1)^2 ≤ n := by
  classical
  -- escolha um primo p | n
  obtain ⟨p, hpprime, hpdiv⟩ := Nat.exists_prime_and_dvd (Nat.ne_of_gt hn1)
  -- de NoSmallPrime: se p ≤ m então p ∤ n; contradição ⇒ m < p
  have hp_gt : m < p := by
    by_contra hpm
    exact (hNSP (q:=p) hpprime (le_of_not_gt hpm)) hpdiv
  have hp_ge : m+1 ≤ p := Nat.succ_le_of_lt hp_gt

  -- escreva n = (n/p) * p
  set q := n / p
  have hmul' : p * (n / p) = n := Nat.mul_div_cancel' hpdiv
  have hqp : p * q = n := by
    simpa [q] using hmul'
  have hmul : q * p = n := by simpa [Nat.mul_comm] using hqp

  -- mostra 2 ≤ q (pois n não é primo ⇒ q ≠ 1 ; e 1 < n ⇒ q ≠ 0)
  have hq_ne0 : q ≠ 0 := by
    intro h
    have h0 : 0 = q * p := by
      simp [h, zero_mul]
    have h0' : 0 = n := by
      simp [hmul] at h0; exact h0
    have hn0 : n = 0 := h0'.symm
    have hnpos : 0 < n := lt_trans (by decide : 0 < 1) hn1
    exact (Nat.ne_of_gt hnpos) hn0
  have hq_ne1 : q ≠ 1 := by
    intro h
    have : p = n := by
      have hh := hmul
      simp [h, one_mul] at hh
      exact hh
    exact hnc ((this ▸ hpprime))
  -- pegue q' primo que divide q; então q' | n e m < q' ≤ q
  obtain ⟨q', hq'prime, hq'div⟩ := Nat.exists_prime_and_dvd (by simpa using hq_ne1)
  have hq'div_n : q' ∣ n := by
    -- q' ∣ q ⇒ q' ∣ q*p = n
    have hqp : q' ∣ q * p := dvd_mul_of_dvd_left hq'div p
    simpa [hmul] using hqp
  have hq'_gt_m : m < q' := by
    -- se q' ≤ m, contradiz hNSP via hq'div_n
    have : ¬ q' ≤ m := by
      intro hle
      exact (hNSP (q:=q') hq'prime hle) hq'div_n
    exact lt_of_not_ge this
  have hq'_le_q : q' ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq_ne0) hq'div
  have hq_ge : m+1 ≤ q := Nat.succ_le_of_lt (lt_of_lt_of_le hq'_gt_m hq'_le_q)

  -- conclui (m+1)^2 ≤ p*q = n
  have hle_pq : (m+1)*(m+1) ≤ p * q := Nat.mul_le_mul hp_ge hq_ge
  have hle_qp : (m+1)*(m+1) ≤ q * p := by
    simpa [Nat.mul_comm] using hle_pq
  have : (m+1)^2 ≤ q * p := by
    simpa [pow_two] using hle_qp
  simpa [hmul] using this

/-- Ponte 1: se `InBlock m 0 n` e `NoSmallPrime m n`, então `n` é primo. -/
lemma prime_of_NoSmallPrime_x0 {m n : Nat}
    (hm : 2 ≤ m) (hB : InBlock m 0 n) (hNSP : NoSmallPrime m n) : Nat.Prime n := by
  rcases hB with ⟨k, hk1, hk2, hn⟩
  by_contra hnp
  -- 1 < n: de m ≥ 2 e k ≥ 1
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmm_pos : 0 < m*m := Nat.mul_pos hm_pos hm_pos
  have hlt_mm1 : 1 < m*m + 1 := Nat.succ_lt_succ hmm_pos
  have h1_le : m*m + 1 ≤ n := by
    have h := Nat.add_le_add_left hk1 (m*m)
    simpa [hn, Nat.mul_zero, Nat.add_assoc] using h
  have hn1 : 1 < n := lt_of_lt_of_le hlt_mm1 h1_le
  have hge : (m+1)^2 ≤ n := comp_ge_sq_of_noSmall hNSP hnp hn1
  -- em x=0 temos n ≤ m^2 + m < (m+1)^2
  have hnR : n ≤ m*m + m := by
    have h := add_le_add_left hk2 (m*m)
    simpa [hn, Nat.mul_zero, Nat.add_assoc] using h
  have : m*m + m < (m+1)^2 := by
    simpa [pow_two] using block0_top_lt m
  exact (not_lt_of_ge hge) (lt_of_le_of_lt hnR this)

/-- Ponte 2: se `InBlock m 1 n` e `NoSmallPrime m n`, então `n` é primo. -/
lemma prime_of_NoSmallPrime_x1 {m n : Nat}
    (hm : 2 ≤ m) (hB : InBlock m 1 n) (hNSP : NoSmallPrime m n) : Nat.Prime n := by
  rcases hB with ⟨k, hk1, hk2, hn⟩
  by_contra hnp
  -- como acima, 2 ≤ n
  have hm_pos : 0 < m := lt_of_lt_of_le (by decide : 0 < 2) hm
  have hmm_pos : 0 < m*m := Nat.mul_pos hm_pos hm_pos
  have hlt_mm1 : 1 < m*m + 1 := Nat.succ_lt_succ hmm_pos
  have h1_le : m*m + 1 ≤ n := by
    -- 1 ≤ m+k (pois 1 ≤ m e 0 ≤ k), então m*m + 1 ≤ m*m + (m + k) = n
    have hm_ge1 : 1 ≤ m := le_trans (by decide : 1 ≤ 2) hm
    have : 1 ≤ m + k := le_trans hm_ge1 (Nat.le_add_right _ _)
    have h := Nat.add_le_add_left this (m*m)
    simpa [hn, Nat.add_assoc, Nat.mul_comm] using h
  have hn1 : 1 < n := lt_of_lt_of_le hlt_mm1 h1_le
  have hge : (m+1)^2 ≤ n := comp_ge_sq_of_noSmall hNSP hnp hn1
  -- em x=1 temos n ≤ m^2 + 2m < (m+1)^2
  have hnR : n ≤ m*m + 2*m := by
    -- a partir de k ≤ m, somamos m dos dois lados e depois m*m
    have hk' : m + k ≤ m + m := add_le_add_left hk2 m
    have hsum : m*m + (m + k) ≤ m*m + (m + m) := add_le_add_left hk' (m*m)
    simpa [hn, Nat.mul_comm, Nat.add_assoc, two_mul] using hsum
  have : m*m + 2*m < (m+1)^2 := by
    simpa [pow_two] using block1_top_lt m
  exact (not_lt_of_ge hge) (lt_of_le_of_lt hnR this)

/-- A partir de `existence_main_all`, existe primo no bloco x=0. -/
lemma exists_prime_in_x0 {m : Nat} (hm : 2 ≤ m)
  (existence_main_all :
      ∀ {m x}, 2 ≤ m → x ≤ 8 → ∃ n, InBlock m x n ∧ NoSmallPrime m n) :
  ∃ p, InBlock m 0 p ∧ Nat.Prime p := by
  rcases existence_main_all (m:=m) (x:=0) hm (by decide) with ⟨n, hB, hNSP⟩
  exact ⟨n, hB, prime_of_NoSmallPrime_x0 hm hB hNSP⟩

/-- A partir de `existence_main_all`, existe primo no bloco x=1. -/
lemma exists_prime_in_x1 {m : Nat} (hm : 2 ≤ m)
  (existence_main_all :
      ∀ {m x}, 2 ≤ m → x ≤ 8 → ∃ n, InBlock m x n ∧ NoSmallPrime m n) :
  ∃ p, InBlock m 1 p ∧ Nat.Prime p := by
  rcases existence_main_all (m:=m) (x:=1) hm (by decide) with ⟨n, hB, hNSP⟩
  exact ⟨n, hB, prime_of_NoSmallPrime_x1 hm hB hNSP⟩

/-! ### Auxiliares de limites para InBlock -/

/-- Para `x=0`: `m^2 < n` e `n ≤ m^2 + m`. -/
lemma ineqs_x0 {m n : Nat} (h : InBlock m 0 n) : m^2 < n ∧ n ≤ m^2 + m := by
  rcases h with ⟨k, hk1, hk2, hn⟩
  -- lower: m^2 < m^2 + k (since k ≥ 1)
  have hlt₁ : m^2 < m^2 + 1 := Nat.lt_succ_self _
  have hle₁ : m^2 + 1 ≤ m^2 + k := Nat.add_le_add_left hk1 _
  have hL : m^2 < m^2 + k := lt_of_lt_of_le hlt₁ hle₁
  -- upper: m^2 + k ≤ m^2 + m (since k ≤ m)
  have hR : m^2 + k ≤ m^2 + m := Nat.add_le_add_left hk2 _
  exact ⟨by simpa [hn, pow_two, Nat.mul_comm] using hL, by simpa [hn, pow_two, Nat.mul_comm] using hR⟩

/-- Para `x=1`: `m^2 + m < n` e `n ≤ m^2 + 2m`. -/
lemma ineqs_x1 {m n : Nat} (h : InBlock m 1 n) : m^2 + m < n ∧ n ≤ m^2 + 2*m := by
  rcases h with ⟨k, hk1, hk2, hn⟩
  -- lower: add a positive k to m^2+m
  have hkpos : 0 < k := Nat.succ_le_iff.mp hk1
  have hL : m^2 + m < m^2 + m + k := by
    simpa [Nat.add_assoc] using Nat.add_lt_add_left hkpos (m^2 + m)
  -- upper: add m on both sides then add m^2
  have hk' : m + k ≤ m + m := Nat.add_le_add_left hk2 _
  have hR : m^2 + (m + k) ≤ m^2 + (m + m) := Nat.add_le_add_left hk' _
  exact ⟨by simpa [hn, Nat.add_assoc, pow_two, Nat.mul_comm] using hL,
         by simpa [hn, Nat.add_assoc, two_mul, pow_two, Nat.mul_comm] using hR⟩

/-- (A) Legendre (conjectura): para todo `n ≥ 2`, existe um primo em `(n^2, (n+1)^2)`.
    Aqui provamos a versão condicional: se `existence_main_all` vale, então Legendre vale.
    Ideia: use `x=0` para `m=n` e as desigualdades do bloco. -/
theorem Legendre_from_mAspero
  (existence_main_all :
      ∀ {m x}, 2 ≤ m → x ≤ 8 → ∃ n, InBlock m x n ∧ NoSmallPrime m n) :
  ∀ n ≥ 2, ∃ p, n^2 < p ∧ p < (n+1)^2 ∧ Nat.Prime p := by
  intro n hn
  rcases exists_prime_in_x0 (m:=n) hn existence_main_all with ⟨p, hB, hp⟩
  have ⟨hL, hR⟩ := ineqs_x0 hB
  -- topo estrito: n^2 + n < (n+1)^2
  have htop : n^2 + n < (n+1)^2 := by
    simpa [pow_two] using block0_top_lt n
  exact ⟨p, hL, lt_of_le_of_lt hR htop, hp⟩

/-- (B) Oppermann (conjectura): para todo `n ≥ 2`, existe um primo em `(n^2-n, n^2)`
    e outro em `(n^2, n^2+n)`. Prova condicional a `existence_main_all`, via `x=0`
    para `m=n` (acima) e `x=1` para `m=n-1` (abaixo). -/
theorem Oppermann_from_mAspero
  (existence_main_all :
      ∀ {m x}, 2 ≤ m → x ≤ 8 → ∃ n, InBlock m x n ∧ NoSmallPrime m n) :
  ∀ n ≥ 2,
    ∃ p₁ p₂,
      n^2 - n < p₁ ∧ p₁ < n^2 ∧
      n^2       < p₂ ∧ p₂ < n^2 + n ∧
      Nat.Prime p₁ ∧ Nat.Prime p₂ := by
  intro n hn
  -- acima: m=n, x=0
  rcases exists_prime_in_x0 (m:=n) hn existence_main_all with ⟨p₂, hB2, hp2⟩
  have ⟨h2L, h2Rle⟩ := ineqs_x0 hB2
  -- força estrito no topo: p₂ ≠ n^2 + n (pois n^2+n = n*(n+1) é composto)
  have h2R' : p₂ < n^2 + n := by
    have hn_ne1 : n ≠ 1 := by
      have : 1 < n := lt_of_lt_of_le (by decide : 1 < 2) hn
      exact Nat.ne_of_gt this
    have hnp1_ne1 : n + 1 ≠ 1 := by
      have : 1 < n + 1 := lt_of_lt_of_le (by decide : 1 < 3) (Nat.succ_le_succ hn)
      exact Nat.ne_of_gt this
    have hcomp : ¬ Nat.Prime (n^2 + n) := by
      have : (n^2 + n) = n * (n + 1) := by
        calc
          n^2 + n = n*n + n := by simp [pow_two]
          _ = n * (n + 1) := by simp [Nat.mul_add]
      simpa [this] using (Nat.not_prime_mul hn_ne1 hnp1_ne1)
    exact lt_of_le_of_ne h2Rle (by intro heq; exact hcomp (heq ▸ hp2))
  -- abaixo: m=n-1, x=1  (trate n=2 à parte)
  by_cases h2 : n = 2
  · -- caso pequeno explícito
    have hLt1 : n^2 - n < 3 := by
      cases h2
      exact Nat.lt_succ_self 2
    have hLt2 : 3 < n^2 := by
      cases h2
      exact Nat.lt_succ_self 3
    exact ⟨3, p₂, hLt1, hLt2, h2L, h2R', Nat.prime_three, hp2⟩
  · -- então n ≥ 3 ⇒ 2 ≤ n-1
    have h3 : 3 ≤ n := by
      have : 2 < n := lt_of_le_of_ne hn (Ne.symm h2)
      exact Nat.succ_le_of_lt this
    -- caminho mais robusto para 2 ≤ n-1
    have hm1 : 2 ≤ n - 1 := Nat.le_pred_of_lt <|
      lt_of_lt_of_le (by decide : 2 < 3) h3
    rcases exists_prime_in_x1 (m:=n-1) hm1 existence_main_all with ⟨p₁, hB1, hp1⟩
    have ⟨h1L, h1Rle⟩ := ineqs_x1 hB1
    -- n^2 - n ≤ (n-1)^2 + (n-1) < p₁
    have h1_lower_le : n^2 - n ≤ (n-1)^2 + (n-1) := by
      have h1le : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
      have hcalc1 : n^2 - n = n * (n - 1) := by
        have h := (Nat.mul_sub_left_distrib n n 1)
        simpa [pow_two, Nat.mul_one] using h.symm
      have hcalc2 : (n-1)^2 + (n-1) = (n-1) * n := by
        calc
          (n-1)^2 + (n-1)
              = (n-1) * (n-1) + (n-1) * 1 := by simp [pow_two]
          _ = (n-1) * ((n-1) + 1) := by
                simp [Nat.mul_add, Nat.add_comm]
          _ = (n-1) * n := by
                have : (n-1) + 1 = n := Nat.sub_add_cancel h1le
                simp [this]
      have : n^2 - n = (n-1)^2 + (n-1) := by
        calc
          n^2 - n = n * (n - 1) := hcalc1
          _ = (n-1) * n := by simp [Nat.mul_comm]
          _ = (n-1)^2 + (n-1) := by simp [hcalc2.symm]
      exact le_of_eq this
    have h1L' : n^2 - n < p₁ := lt_of_le_of_lt h1_lower_le h1L
    -- topo estrito: p₁ ≤ (n-1)^2 + 2(n-1) < n^2
    have h1R' : p₁ < n^2 := by
      -- (n-1)^2 + 2(n-1) + 1 = ((n-1)+1)^2 = n^2 ⇒ topo < n^2
      have hx : (n-1)^2 + 2*(n-1) < (n-1)^2 + 2*(n-1) + 1 := Nat.lt_succ_self _
      have hsq_eq : (n-1)^2 + 2*(n-1) + 1 = ((n-1) + 1)^2 := by
        simp [pow_two, two_mul, Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
          Nat.add_assoc]
      have h1le : 1 ≤ n := le_trans (by decide : 1 ≤ 2) hn
      have hk : (n-1) + 1 = n := Nat.sub_add_cancel h1le
      have hx2 : (n-1)^2 + 2*(n-1) + 1 = n^2 := by simpa [hk] using hsq_eq
      have htop : (n-1)^2 + 2*(n-1) < n^2 := lt_of_lt_of_eq hx hx2
      exact lt_of_le_of_lt h1Rle htop
    exact ⟨p₁, p₂, h1L', h1R', h2L, h2R', hp1, hp2⟩

/-- (C) Brocard (conjectura): para primos `p<q` consecutivos, existem pelo menos
    4 primos entre `p^2` e `q^2`. Nesta formalização retornamos explicitamente
    quatro números `a b c d` acompanhados das provas de que são primos e de que
    pertencem ao intervalo aberto `(p^2, q^2)`. A prova vale condicionalmente a
    `existence_main_all`,
    sob a hipótese `q ≥ p+2`, suficiente para todos os pares consecutivos exceto o
    caso pequeno `(p,q)=(2,3)`. Na prática:
    - para consecutivos com `p ≥ 3`, temos automaticamente `q ≥ p+2`;
    - para `(2,3)`, o intervalo `(4,9)` possui somente dois primos (5 e 7), logo é um
      caso especial fora do escopo do enunciado “≥ 4”. -/
theorem Brocard_from_mAspero
  (existence_main_all :
      ∀ {m x}, 2 ≤ m → x ≤ 8 → ∃ n, InBlock m x n ∧ NoSmallPrime m n) :
  ∀ {p q}, Nat.Prime p → Nat.Prime q → p + 2 ≤ q →
    ∃ a b c d,
      p^2 < a ∧ a < q^2 ∧ Nat.Prime a ∧
      p^2 < b ∧ b < q^2 ∧ Nat.Prime b ∧
      p^2 < c ∧ c < q^2 ∧ Nat.Prime c ∧
      p^2 < d ∧ d < q^2 ∧ Nat.Prime d ∧
      a < b ∧ b < c ∧ c < d := by
  intro p q hp hq hpq
  have hp2 : 2 ≤ p := hp.two_le
  -- dois do m = p (x=0,1)
  rcases exists_prime_in_x0 (m:=p) hp2 existence_main_all with ⟨a, haB, haP⟩
  rcases exists_prime_in_x1 (m:=p) hp2 existence_main_all with ⟨b, hbB, hbP⟩
  have ⟨haL, haRle⟩ := ineqs_x0 haB
  have ⟨hbL_strict, hbRle⟩ := ineqs_x1 hbB
  -- limites superiores sob q^2
  have h_p1_le_q : p+1 ≤ q := by
    exact le_trans (Nat.le_succ (p+1)) hpq
  have h_p2_le_q : p+2 ≤ q := hpq
  have hsq1 : (p+1)^2 ≤ q^2 := by
    have h := Nat.mul_le_mul h_p1_le_q h_p1_le_q
    simpa [pow_two] using h
  have hsq2 : (p+2)^2 ≤ q^2 := by
    have h := Nat.mul_le_mul h_p2_le_q h_p2_le_q
    simpa [pow_two] using h
  -- a: p^2 < a < q^2
  have haU : a < q^2 := by
    have a_lt_p1sq : a < (p+1)^2 :=
      lt_of_le_of_lt haRle (by simpa [pow_two] using block0_top_lt p)
    exact lt_of_lt_of_le a_lt_p1sq hsq1
  -- b: p^2 < b (pois p ≥ 2 ⇒ p > 0 ⇒ p^2 < p^2 + p < b)
  have hp_pos : 0 < p := lt_of_lt_of_le (by decide : 0 < 2) hp2
  have hbL : p^2 < b := by
    have : p^2 < p^2 + p := by exact Nat.lt_add_of_pos_right (by exact hp_pos)
    exact lt_trans this hbL_strict
  have hbU : b < q^2 := by
    have hb_lt_p1sq : b < (p+1)^2 :=
      lt_of_le_of_lt hbRle (by simpa [pow_two] using block1_top_lt p)
    exact lt_of_lt_of_le hb_lt_p1sq hsq1
  -- dois do m = p+1 (x=0,1)
  have hpp2 : 2 ≤ p+1 := le_trans hp2 (Nat.le_succ _)
  rcases exists_prime_in_x0 (m:=p+1) hpp2 existence_main_all with ⟨c, hcB, hcP⟩
  rcases exists_prime_in_x1 (m:=p+1) hpp2 existence_main_all with ⟨d, hdB, hdP⟩
  have ⟨hcL, hcRle⟩ := ineqs_x0 hcB
  have ⟨hdL_strict, hdRle⟩ := ineqs_x1 hdB
  -- c lower: p^2 < (p+1)^2 < c
  have cL : p^2 < c := lt_trans (by simpa [pow_two] using sq_lt_succ_sq p) hcL
  -- d lower: (p+1)^2 + (p+1) < d ⇒ (p+1)^2 < d ⇒ p^2 < d
  have hpp_lt : p^2 < (p+1)^2 := by simpa [pow_two] using sq_lt_succ_sq p
  have hstep : (p+1)^2 < (p+1)^2 + (p+1) := by
    have : 0 < p+1 := Nat.succ_pos _
    exact Nat.lt_add_of_pos_right this
  have dL : p^2 < d := lt_trans hpp_lt (lt_trans hstep hdL_strict)
  -- c,d upper under q^2 via (p+2)^2 ≤ q^2
  have cU : c < q^2 := by
    have c_lt_p2sq : c < (p+2)^2 :=
      lt_of_le_of_lt hcRle (by simpa [pow_two] using succ_block_bridge p)
    exact lt_of_lt_of_le c_lt_p2sq hsq2
  have dU : d < q^2 := by
    have d_lt_p2sq : d < (p+2)^2 :=
      lt_of_le_of_lt hdRle (by simpa [pow_two] using block1_top_lt (p+1))
    exact lt_of_lt_of_le d_lt_p2sq hsq2
  -- distinção (ordem estrita): a < b < c < d
  have hab : a < b := by
    have : a ≤ p^2 + p := haRle
    exact lt_of_le_of_lt this hbL_strict
  have hbc : b < c := by
    have hb_top : b ≤ p^2 + 2*p := hbRle
    -- p^2 + 2*p < p^2 + 2*p + 1 is trivial
    have hsucc : p^2 + 2*p < p^2 + 2*p + 1 := Nat.lt_succ_self (p^2 + 2*p)
    -- p^2 + 2*p + 1 = (p+1)^2
    have hsum_sq : p^2 + 2*p + 1 = (p+1)^2 := by
      simp [pow_two, two_mul, Nat.mul_add, Nat.add_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc]
    -- combine to get b < (p+1)^2
    have hb_lt_succsq : b < (p+1)^2 := by
      have : b < p^2 + 2*p + 1 := lt_of_le_of_lt hb_top hsucc
      simpa [hsum_sq] using this
    exact lt_trans hb_lt_succsq hcL
  have hcd : c < d := by
    have : c ≤ (p+1)^2 + (p+1) := hcRle
    exact lt_of_le_of_lt this hdL_strict
  exact ⟨a, b, c, d,
    haL, haU, haP,
    hbL, hbU, hbP,
    cL, cU, hcP,
    dL, dU, hdP,
    hab, hbc, hcd⟩
