/-
SPDX-License-Identifier: Apache-2.0
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Defs
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.Interface
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.Log10Bounds
import RoughBlocks.Heavy.Buchstab.CoreB
import RoughBlocks.Heavy.Buchstab.Equation
-- import RoughBlocks.Heavy.Buchstab.Monotonicity
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Monotonicity

namespace RoughBlocks.Heavy.Application

open Classical
open RoughBlocks
open RoughBlocks.Heavy
open RoughBlocks.Heavy.Numeric
open RoughBlocks.External.Certs

-- /-- **Enunciado final (por bloco)**:
-- Para todo `m ≥ 18794` e todo bloco `x : Fin 9`, existe `k ∈ K m x` com `mRough m k`.

-- Observação: recebe um `H : UniformBridgeFrom_m0`, que é exatamente
-- o adaptador exposto pelo módulo de Monotonicidade/Bridge. -/
-- theorem exists_allNine_ge_18794_final
--   (H : UniformBridgeFrom_m0) {m : ℕ} (hm : (18794 : ℕ) ≤ m) (x : Fin 9) :
--   ∃ k ∈ K m (x : ℕ), mRough m k := by
--   -- No seu setup, `m0 = 18794` é definicional; rfl fecha.
--   have h_m0 : RoughBlocks.External.Certs.UniformLB18794Bridge.m0 = (18794 : ℕ) := rfl
--   simpa using
--     (RoughBlocks.External.Certs.exists_allNine_ge_18794_using_H
--        (H := H) (m := m) (hm := hm) (h_m0_eq_18794 := h_m0) x)

-- /-- **Enunciado final (todos os blocos)**:
-- Para todo `m ≥ 18794`, cada um dos 9 blocos contém pelo menos um `m`-áspero. -/
-- theorem exists_allNine_ge_18794_final_all
--   (H : UniformBridgeFrom_m0) {m : ℕ} (hm : (18794 : ℕ) ≤ m) :
--   ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
--   intro x
--   exact exists_allNine_ge_18794_final (H := H) (m := m) hm x

-- /-- **Versão sem `Fin`** (conveniência): para `x ≤ 8`. -/
-- theorem exists_block_ge_18794_final_nat
--   (H : UniformBridgeFrom_m0) {m x : ℕ} (hm : (18794 : ℕ) ≤ m) (hx : x ≤ 8) :
--   ∃ k ∈ K m x, mRough m k := by
--   -- sobe `x` para `Fin 9`
--   refine ?_
--   let x9 : Fin 9 := ⟨x, Nat.lt_succ_of_le hx⟩
--   have := exists_allNine_ge_18794_final (H := H) (m := m) hm x9
--   simpa using this




-- /-- Adaptador canônico: junta as duas pontes uniformes já certificadas para `m ≥ m0`. -/
-- def H18794 : UniformBridgeFrom_m0 where
--   fL_le_margin_ge_m0 := UniformLB18794Bridge.fL_le_margin_ge_m0
--   LB_le_PhiDiff_ge_m0 := UniformGE18794Bridge.LB_le_PhiDiff_ge_m0

-- /-- Versão “sem H”: só precisa de `m ≥ 18794` e `x ≤ 8`. -/
-- theorem exists_block_ge_18794_final_nat_noHyp
--   {m x : ℕ} (hm : (18794 : ℕ) ≤ m) (hx : x ≤ 8) :
--   ∃ k ∈ K m x, mRough m k :=
-- by
--   -- usa o wrapper que recebe H, instanciando com o adaptador canônico
--   exact RoughBlocks.Heavy.Application.exists_block_ge_18794_final_nat
--     (H := H18794) (m := m) (x := x) hm hx



/--
Wrapper “ponto a ponto”: para todo `m ≥ 18794` e todo `x ≤ 8`,
existe `k ∈ K m x` tal que `mRough m k`.

Depende apenas do adaptador `H : UniformBridgeFrom_m0` já provido pelos seus certificados.
-/
theorem exists_block_ge_18794_final_nat
  (H : UniformBridgeFrom_m0) {m x : ℕ} (hm : 18794 ≤ m) (hx : x ≤ 8) :
  ∃ k ∈ K m x, mRough m k := by
  -- converte `x ≤ 8` em `Fin 9`
  let x9 : Fin 9 := ⟨x, Nat.lt_succ_of_le hx⟩
  -- aplica o teorema já provado na camada de Certs/Monotonicity
  obtain ⟨k, hkK, hkR⟩ :=
    exists_allNine_ge_18794_using_H (H := H) (m := m) (hm := hm) (x := x9)
      (h_m0_eq_18794 := rfl)
  -- adapta o tipo do índice de volta para `x : ℕ`
  exact ⟨k, by simpa using hkK, hkR⟩

/-- Versão “todos os blocos de uma vez”: para `m ≥ 18794`, cada bloco tem pelo menos um `m`-áspero. -/
theorem exists_allNine_ge_18794_final_nat
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : 18794 ≤ m) :
  ∀ x : Fin 9, ∃ k ∈ K m (x : ℕ), mRough m k := by
  intro x
  have hx : (x : ℕ) ≤ 8 := Nat.le_of_lt_succ x.2
  simpa using exists_block_ge_18794_final_nat (H := H) (m := m) (x := (x : ℕ)) hm hx


/-- Versão pontual (sem `hx`): dada `x : Fin 9`. -/
theorem exists_allNine_ge_18794_final_nat_pt
  (H : UniformBridgeFrom_m0) {m : ℕ} (hm : 18794 ≤ m) (x : Fin 9) :
  ∃ k ∈ K m (x : ℕ), mRough m k :=
by
  -- usa a versão "∀ blocos" já provada e especializa em `x`
  exact (exists_allNine_ge_18794_final_nat (H := H) (m := m) hm) x

#print axioms RoughBlocks.Heavy.Application.exists_allNine_ge_18794_final_nat_pt
#check RoughBlocks.Heavy.Application.exists_allNine_ge_18794_final_nat_pt

end RoughBlocks.Heavy.Application
