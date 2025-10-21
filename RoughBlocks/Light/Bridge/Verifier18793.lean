/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025

Parte do projeto RoughBlocks.
Base formal para verificação de certificados (intervalos) do caso ≥ 18793.
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section

namespace RoughBlocks.Light.BridgeVerifier

/-!
  Núcleo mínimo de aritmética intervalar provada correta.
  Mantemos a estrutura simples e exigimos as hipóteses necessárias em cada lema,
  sem `sorry`.
-/

structure Interval where
  lo : ℝ
  hi : ℝ

def Mem (x : ℝ) (I : Interval) : Prop := I.lo ≤ x ∧ x ≤ I.hi

notation:50 x:50 " ∈I " I:50 => Mem x I

@[simp] lemma mem_mk {x a b : ℝ} : x ∈I Interval.mk a b ↔ a ≤ x ∧ x ≤ b := Iff.rfl

-- Constantes úteis como intervalos degenerados
def constI (c : ℝ) : Interval := ⟨c, c⟩

@[simp] lemma mem_constI {x c : ℝ} : x ∈I constI c ↔ x = c := by
  constructor
  · intro hx; exact le_antisymm hx.2 hx.1
  · intro hx; subst hx; exact And.intro le_rfl le_rfl

/-! (Operações e lemas detalhados de intervalos foram omitidos por ora
    pois não são necessários para a integração atual dos certificados.) -/

end RoughBlocks.Light.BridgeVerifier
