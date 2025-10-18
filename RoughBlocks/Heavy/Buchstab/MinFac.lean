/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton Costa Ribeiro

Part of the RoughBlocks project.
This file is licensed under the Apache License 2.0 (see LICENSE).
Docs/paper are under CC BY-NC-ND 4.0 (see LICENSE-docs-CC-BY-NC-ND).
-/

import Mathlib

/-!
# Elementos básicos sobre `Nat.minFac`

Lemas auxiliares usados na etapa de decomposição à la Buchstab.

## Conteúdo

* `minFac_prime_of_two_le` — para `n ≥ 2`, o fator mínimo `minFac n` é primo.
* `minFac_le_of_prime_dvd` — se um primo `p` divide `n`, então `minFac n ≤ p`.
* `minFac_dvd_eq` — fatorização simples: `n = minFac n * (n / minFac n)`.

As provas são uma **camada fina** sobre lemas padrão de `Mathlib`.
-/

namespace RoughBlocks.Heavy

/-- Para `n ≥ 2`, o fator mínimo `minFac n` é primo. -/
lemma minFac_prime_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    Nat.Prime (Nat.minFac n) := by
  have hne : n ≠ 1 := ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hn)
  exact Nat.minFac_prime hne

/-- Se `p` é primo e `p ∣ n`, então `minFac n ≤ p`. -/
lemma minFac_le_of_prime_dvd {n p : ℕ}
    (hp : Nat.Prime p) (hpdiv : p ∣ n) :
    Nat.minFac n ≤ p :=
  Nat.minFac_le_of_dvd (Nat.Prime.two_le hp) hpdiv

/-- Fatorização “canônica” por `minFac`: `n = minFac n * (n / minFac n)`. -/
lemma minFac_dvd_eq (n : ℕ) :
    ∃ m : ℕ, n = Nat.minFac n * m := by
  have hmin : Nat.minFac n ∣ n := Nat.minFac_dvd n
  refine ⟨n / Nat.minFac n, ?_⟩
  -- Em `ℕ`, `mul_div_cancel'` dá `(n / a) * a = n` quando `a ∣ n`.
  simpa [Nat.mul_comm] using (Nat.mul_div_cancel' hmin).symm

end RoughBlocks.Heavy
