/-
SPDX-License-Identifier: Apache-2.0
Copyright (c) 2025 Marilton
Part of the RoughBlocks project.
-/

import Mathlib
import RoughBlocks.Heavy.Numeric
import RoughBlocks.Heavy.WindowLink.Block
import RoughBlocks.Heavy.WindowLink.BridgeLBtoPhiDiff
import RoughBlocks.Heavy.WindowLink.Bridge_fL_to_Margin
import RoughBlocks.External.Certs.AllNine_Framework
import RoughBlocks.External.Certs.UniformGE18794Bridge
import RoughBlocks.External.Certs.UniformLB18794Monotonicity
import RoughBlocks.External.BridgeFromCert18794
import RoughBlocks.External.Certs.FullVerifier

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
-/

/-- Parâmetro-alvo do projeto. -/
def m0 : ℕ := 18794

lemma m0_ge_bridge_threshold : BridgeThreshold ≤ m0 := by decide
lemma m0_ge_two              : 2 ≤ m0               := by decide
lemma m0_ge_2981             : 2981 ≤ m0            := by decide

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

/-! ## 4 lemas-ponte nas formas que o teorema externo exige ---------------- -/

/-- (1) Margem ≤ margem de papel para `m ≥ m0`.
    Apesar do nome do lema base, ele exige `2981 ≤ m`.
    Como `m0 ≥ 2981` e `m ≥ m0`, obtemos `2981 ≤ m`. -/
lemma margin_le_marginPaper_from_18794 (m : ℕ) (hm : m0 ≤ m) :
  Numeric.margin m ≤ Numeric.marginPaper m := by
  have hm2981 : 2981 ≤ m := le_trans m0_ge_2981 hm
  exact Numeric.margin_le_marginPaper_of_ge_two hm2981

/-- (2) `LB ≤ count` a partir do certificado verificado (SEM axioma local).
    Recebe o recibo `hcert_full` como parâmetro, sem `by decide`. -/
lemma LB_le_count_from_cert
  (m : ℕ) (hm : m0 ≤ m) (x : Fin 9)
  (hcert_full : RoughBlocks.External.Certs.FullVerifier.verify_full_certificate = true) :
  Numeric.LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ) := by
  have hm' : 18794 ≤ m := by simpa [m0] using hm
  have hx  : (x : ℕ) ≤ 8 := coe_fin9_le_eight x
  -- O bridge externo já fornece exatamente LB ≤ count no mesmo (m,x):
  simpa using
    (RoughBlocks.External.bridge_ge_18794_from_verified_certificate hcert_full hm' hx)

/-- (3) Família `hL`: `∀ x, LB(m,x) ≤ External.Certs.PhiDiffAt(m,x)`,
    encadeando (2) com a identidade de janela `count = Φ` (orientação correta). -/
lemma hL_family_from_18794
  (m : ℕ) (hm : m0 ≤ m)
  (hcert_full : RoughBlocks.External.Certs.FullVerifier.verify_full_certificate = true) :
  ∀ x : Fin 9,
    Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ) := by
  intro x
  have hx  : (x : ℕ) ≤ 8 := coe_fin9_le_eight x
  have hm2 : 2 ≤ m       := m0_ge_two.trans hm
  -- 1) LB ≤ count (do certificado)
  have hLC :=
    LB_le_count_from_cert (m := m) (hm := hm) (x := x) (hcert_full := hcert_full)
  -- 2) count = PhiDiffAt(Heavy) no próprio m (argumentos posicionais)
  have hEq :=
    countRoughInBlock_eq_phiDiff_succ_real (m := m) (x := (x : ℕ)) hm2 hx
  -- 3) reescreve RHS para a versão `External` e fecha
  simpa [PhiDiff_heavy_eq_certs m (x : ℕ), RoughBlocks.Heavy.PhiDiffAt, hEq] using hLC



#print axioms margin_le_marginPaper_from_18794
#check margin_le_marginPaper_from_18794


/-! ## 2) Teorema principal no estilo “framework” -/

/-- **Existência para `m ≥ 18794` nos 9 blocos** (forma framework).

Recebe como entrada as famílias:
* `hF`: `fL ≤ margin` (vem tipicamente do bridge uniforme/externo);
* `hL`: `LB ≤ PhiDiffAt` (vem do certificado + ponte 2, por ex.).

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

/-! ## 3) Famílias auxiliares prontas ------------------------------------ -/

/-- Constrói `hL` a partir de uma família `LB ≤ count` (ponte 2). -/
lemma hL_family_from_LB_count
    {m : ℕ} (hm : m0 ≤ m)
    (hLBcount :
      ∀ x : Fin 9,
        Numeric.LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ)) :
    ∀ x : Fin 9,
      Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ) := by
  intro x
  have hm2 : 2 ≤ m := m0_ge_two.trans hm
  have hx : (x : ℕ) ≤ 8 := coe_fin9_le_eight x
  -- ponte 2 já pronta no módulo WindowLink
  have h :=
    RoughBlocks.Heavy.LB_le_PhiDiff (m := m) (x := (x : ℕ)) hm2 hx (hLBcount x)
  simpa [PhiDiff_heavy_eq_certs m (x : ℕ)] using h

/-- Família `LB ≤ count` produzida diretamente pelo certificado. -/
lemma hLBcount_from_certificate
    (m : ℕ) (hm : m0 ≤ m) :
    ∀ x : Fin 9,
      Numeric.LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ) := by
  intro x
  have hcert :
    RoughBlocks.External.Certs.FullVerifier.verify_full_certificate = true :=
    RoughBlocks.External.Certs.FullVerifier.full_certificate_is_valid
  have hm₀ : (18794 : ℕ) ≤ m := by simpa [m0] using hm
  have hx : (x : ℕ) ≤ 8 := coe_fin9_le_eight x
  simpa using
    RoughBlocks.External.bridge_ge_18794_from_verified_certificate hcert hm₀ hx

/-- Família `LB ≤ PhiDiffAt` derivada automaticamente do certificado uniforme. -/
lemma hL_family_from_certificate
    (m : ℕ) (hm : m0 ≤ m) :
    ∀ x : Fin 9,
      Numeric.LB m (x : ℕ) ≤ External.Certs.PhiDiffAt m (x : ℕ) :=
  hL_family_from_LB_count (m := m) hm (hLBcount_from_certificate m hm)

/-- Variante prática: parte apenas de `hLBcount` para construir `hL`
    e instanciar o teorema externo. -/
theorem exists_mRough_from_18794_of_LB_count
    {m : ℕ} (hm : m0 ≤ m)
    (hF : ∀ x : Fin 9, External.Certs.fL x (Real.log (m : ℝ)) ≤ Numeric.margin m)
    (hLBcount :
      ∀ x : Fin 9,
        Numeric.LB m (x : ℕ) ≤ (RoughBlocks.countRoughInBlock m (x : ℕ) : ℝ))
    (x : Fin 9) :
    ∃ k ∈ K m (x : ℕ), mRough m k := by
  have hL := hL_family_from_LB_count (m := m) hm hLBcount
  exact exists_mRough_from_18794 hm hF hL x

/-! ## 4) Ponte “fL → PhiDiff” genérica (útil no dia-a-dia) --------------- -/

/-- **Agregador de ponte**.

Dado `m` na faixa formal, se:
* `BridgeThreshold ≤ m` e `2 ≤ m`;
* `margin m ≤ marginPaper m`;
* `∀ x, fL(x, log m) ≤ margin m` (família computacional);
* `∀ x, LB(m,x) ≤ countRoughInBlock(m,x)` (gancho Buchstab local),

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

/-! ## 5) Sanity ----------------------------------------------------------- -/

--#print axioms exists_mRough_from_18794
--#check exists_mRough_from_18794

end RoughBlocks.Heavy
