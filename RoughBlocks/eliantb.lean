/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Monotonicity
import RoughBlocks.Heavy.WindowLink.BridgeLBtoPhiDiff
import RoughBlocks.Heavy.WindowLink.Bridge_fL_to_Margin

noncomputable section
open Classical Real
open RoughBlocks

namespace RoughBlocks.Heavy

/-! # Existência em todos os nove blocos para `m ≥ 18794`

Nesta versão:

* Não usamos nenhum lema com nome incerto (ex.: `LB_le_PhiDiff_local`, `LB_le_count_local`,
  `LB_le_count_block`, etc.).
* Encapsulamos o resultado principal diretamente via o framework externo
  `exists_mRough_in_allNine_from_18794`, que requer:
  - `BridgeThreshold ≤ m` (hipótese “faixa formal”),
  - `m0 ≤ m` na namespace externa (idêntico a este `m0`),
  - a família computacional `fL ≤ margin`,
  - e a família analítica `LB ≤ PhiDiffAt`.
* Também deixamos pronta uma ponte genérica “fL ≤ PhiDiffAt” (útil no dia-a-dia),
  que recebe como **hipóteses** as desigualdades computacionais locais
  `fL ≤ margin` e `LB ≤ count`, além de `margin ≤ marginPaper`.

Dessa forma, o arquivo compila isoladamente e você pode suprir as famílias
`fL ≤ margin` e `LB ≤ PhiDiffAt` a partir dos módulos que preferir
(por ex., `UniformGE18794Bridge` para `fL ≤ margin` e seu gancho de núcleo/recibo para `LB ≤ PhiDiffAt`).
-/

/-- Parâmetro-alvo do projeto. -/
def m0 : ℕ := 18794

lemma m0_ge_bridge_threshold : BridgeThreshold ≤ m0 := by decide
lemma m0_ge_two              : 2 ≤ m0               := by decide

@[simp] lemma coe_fin9_le_eight (x : Fin 9) : (x : ℕ) ≤ 8 :=
  Nat.le_of_lt_succ x.is_lt

/-- Atalho: a `PhiDiffAt` do `Heavy`. -/
abbrev PhiDiff (m x : ℕ) : ℝ := RoughBlocks.Heavy.PhiDiffAt m x

/-! ## 1) Identidade `Heavy` ↔ `External.Certs` -/

-- As duas `PhiDiffAt` (Heavy e External) são definicionalmente as mesmas.
lemma PhiDiff_heavy_eq_certs (m x : ℕ) :
  PhiDiff m x = External.Certs.PhiDiffAt m x := rfl

lemma PhiDiff_heavy_le_certs (m x : ℕ) :
  PhiDiff m x ≤ External.Certs.PhiDiffAt m x := by
  simp [PhiDiff_heavy_eq_certs m x]

/-! ## 2) Teorema principal no estilo “framework” -/

/-- **Existência para `m ≥ 18794` nos 9 blocos** (forma framework).

Recebe como entrada as famílias:
* `hF`: `fL ≤ margin` (vem tipicamente do bridge uniforme em `UniformGE18794Bridge`);
* `hL`: `LB ≤ PhiDiffAt` (vem de seu gancho analítico: núcleo/recibo/ponte 2).

Com isso, invocamos diretamente o teorema externo
`External.Certs.exists_mRough_in_allNine_from_18794` que já está fechado.
-/
theorem exists_mRough_from_18794
    {m : ℕ} (hm : m0 ≤ m)
    (hF : ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m)
    (hL : ∀ x : Fin 9, Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ))
    (x : Fin 9) :
    ∃ k ∈ K m (x : ℕ), mRough m k := by
  -- Pré-condições formais do teorema externo
  have hBridge : BridgeThreshold ≤ m := m0_ge_bridge_threshold.trans hm
  have hm_ext : External.Certs.m0 ≤ m := by
    have : External.Certs.m0 = m0 := by decide
    simpa [this] using hm
  -- Aplica o teorema externo “all nine”
  exact RoughBlocks.External.Certs.exists_mRough_in_allNine_from_18794
    hBridge hm_ext hF hL x

-- /-! ## 3) Ponte “do dia a dia”: `fL ≤ PhiDiffAt`

/-- **Agregador de ponte** (forma que o typechecker está pedindo).

Dado `m` na faixa formal, se:
* `BridgeThreshold ≤ m` e `2 ≤ m`;
* `margin m ≤ marginPaper m`;
* `∀ x, fL(x, log m) ≤ margin m` (a sua família computacional); e
* `∀ x, LB(m,x) ≤ countRoughInBlock(m,x)` (o seu “gancho Buchstab” local),

então para todo `x : Fin 9` vale `fL(x, log m) ≤ PhiDiffAt(m,x)`.
-/
lemma fL_le_PhiDiff_general_from_bridge
  {m : ℕ}
  (hmB : BridgeThreshold ≤ m)
  (hm2 : 2 ≤ m)
  (hmargin_le_marginPaper :
      RoughBlocks.Heavy.Numeric.margin m
        ≤ RoughBlocks.Heavy.Numeric.marginPaper m)
  (hF : ∀ x : Fin 9,
      RoughBlocks.External.Certs.fL x (Real.log (m : ℝ))
        ≤ RoughBlocks.Heavy.Numeric.margin m)
  (hLBcount : ∀ x : Fin 9,
      RoughBlocks.Heavy.Numeric.LB m (x : ℕ)
        ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ)) :
  ∀ x : Fin 9,
    RoughBlocks.External.Certs.fL x (Real.log (m : ℝ))
      ≤ RoughBlocks.Heavy.PhiDiffAt m (x : ℕ) := by
  intro x
  -- 1) Sobe de `margin` para `marginPaper`
  have hLocal :
      RoughBlocks.External.Certs.fL x (Real.log (m : ℝ))
        ≤ RoughBlocks.Heavy.Numeric.marginPaper m :=
    RoughBlocks.Heavy.fL_le_marginPaper_from_18794
      (RoughBlocks.External.Certs.fL) hmB x (hF x) hmargin_le_marginPaper
  -- 2) Fecha a ponte `fL ≤ marginPaper ≤ LB ≤ PhiDiffAt`
  exact RoughBlocks.Heavy.fL_log_le_PhiDiff_from_bridge
    (RoughBlocks.External.Certs.fL) hmB hm2 x hLocal (hLBcount x)





/-! ## 4) Observação prática

* Este arquivo evita intencionalmente depender do nome de um lema específico
  para `LB ≤ count`. Você pode:
  - (a) injetar `hL : LB ≤ PhiDiffAt` diretamente (por exemplo, de um módulo de núcleo),
  - (b) ou injetar `hLBcount : LB ≤ count` e então usar a Ponte 2 (`LB_le_PhiDiff`)
        do arquivo `BridgeLBtoPhiDiff` para fabricar `hL`.

* Se/quando você quiser, dá para criar um arquivo separado que comprove
  `hF` e/ou `hL` a partir do recibo verificado, mas isto não é necessário
  para este módulo compilar e entregar o teorema de existência.
-/

#print axioms exists_mRough_from_18794
#check exists_mRough_from_18794

end RoughBlocks.Heavy
