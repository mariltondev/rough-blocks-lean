import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Basic

open MeasureTheory
open Set intervalIntegral
open scoped Interval

set_option maxHeartbeats 20000000
set_option maxRecDepth 300
set_option diagnostics.threshold 100

/-! # Blocos, soma de blocos e utilidades
    Organização não-disruptiva, com comentários curtos.
-/

-- ########################
-- ## 1) Definições base ##
-- ########################

/-- Integral do bloco unitário `[X+n, X+n+1]`. -/
noncomputable def blockIntegral (F : ℝ → ℝ) (X n : ℕ) : ℝ :=
  ∫ t in (↑X + ↑n)..(↑X + ↑n + 1), F t

/-- Integral total em `[X, X+Y]`. -/
noncomputable def totalIntegral (F : ℝ → ℝ) (X Y : ℕ) : ℝ :=
  ∫ t in (↑X)..(↑X + ↑Y), F t

/-- Soma dos blocos de `X` até `X+Y-1`. -/
noncomputable def blocksSum (F : ℝ → ℝ) (X Y : ℕ) : ℝ :=
  Finset.sum (Finset.range Y) (fun n => blockIntegral F X n)

/-- Termo de Abel no bloco `n`. -/
noncomputable def abelTerm (g : ℝ → ℝ) (A_y : ℕ → ℝ → ℝ) (y X n : ℕ) : ℝ :=
  (A_y y (↑X + ↑n)) * (g (↑X + ↑n + 1) - g (↑X + ↑n))

-- ########################################
-- ## 2) Aditividade e “splitting” local  ##
-- ########################################

/-- C1. Aditividade em intervalos adjacentes (forma orientada). -/
lemma integral_add_adjacent_oriented
  (f : ℝ → ℝ) {a b c : ℝ}
  (h₁ : IntervalIntegrable f (μ := volume) a b)
  (h₂ : IntervalIntegrable f (μ := volume) b c) :
  ∫ t in a..c, f t = (∫ t in a..b, f t) + (∫ t in b..c, f t) := by
  exact (intervalIntegral.integral_add_adjacent_intervals
           (μ := volume) (a := a) (b := b) (c := c)
           (f := f) h₁ h₂).symm

/-- Divide `[X, X+(k+1)]` como `[X, X+k]` + `[X+k, X+k+1]`. -/
lemma integral_split_step
  (F : ℝ → ℝ) (X k : ℕ)
  (hL : IntervalIntegrable F (μ := volume) (↑X) (↑X + ↑k))
  (hR : IntervalIntegrable F (μ := volume) (↑X + ↑k) (↑X + ↑k + 1)) :
  ∫ t in (↑X)..(↑X + (↑k + 1)), F t
    = (∫ t in (↑X)..(↑X + ↑k), F t)
      + (∫ t in (↑X + ↑k)..(↑X + ↑k + 1), F t) := by
  have eq_cast : (↑X + ↑k + 1 : ℝ) = (↑X + (↑k + 1) : ℝ) := by ring
  rw [← eq_cast]
  exact integral_add_adjacent_oriented F hL hR

/-- Soma de `k` blocos mais o bloco `k` é a soma de `k+1` blocos. -/
lemma sum_add_next_block
  (F : ℝ → ℝ) (X k : ℕ) :
  (Finset.sum (Finset.range k)
      (fun n => ∫ t in (↑X + ↑n)..(↑X + ↑n + 1), F t))
    + (∫ t in (↑X + ↑k)..(↑X + ↑k + 1), F t)
    =
  Finset.sum (Finset.range (k + 1))
    (fun n => ∫ t in (↑X + ↑n)..(↑X + ↑n + 1), F t) := by
  rw [Finset.sum_range_succ]

/-- Caso base do “splitting”: integral em `[X, X+0]` é `0`. -/
lemma integral_split_blocks_base
  (F : ℝ → ℝ) (X : ℕ) :
  ∫ t in (↑X)..(↑X + ↑0), F t = 0 := by
  simp

/-- Reempacotamento: passo de splitting com `blockIntegral`. -/
lemma blockIntegral_add
  (F : ℝ → ℝ) (X n : ℕ)
  (hint₁ : IntervalIntegrable F (μ := volume) (↑X) (↑X + ↑n))
  (hint₂ : IntervalIntegrable F (μ := volume) (↑X + ↑n) (↑X + ↑n + 1)) :
  ∫ t in (↑X)..(↑X + ↑(n + 1)), F t
    = (∫ t in (↑X)..(↑X + ↑n), F t) + blockIntegral F X n := by
  simpa [blockIntegral] using integral_split_step F X n hint₁ hint₂


-- #########################################
-- ## 3) Cadeia de integrabilidade global ##
-- #########################################

/-- Caso base da integrabilidade acumulada: `[X, X+1]`. -/
lemma intervalIntegrable_block_base
  (F : ℝ → ℝ) (X : ℕ)
  (hint : IntervalIntegrable F (μ := volume) (X : ℝ) (X + 1 : ℝ)) :
  IntervalIntegrable F (μ := volume) (X : ℝ) (X + 1 : ℝ) :=
  hint

/-- Passo indutivo: concatena `[X, X+k]` e `[X+k, X+k+1]`. -/
lemma intervalIntegrable_block_succ
  (F : ℝ → ℝ) (X k : ℕ)
  (hL : IntervalIntegrable F (μ := volume) (X : ℝ) (X + k : ℝ))
  (hR : IntervalIntegrable F (μ := volume) (X + k : ℝ) (X + k + 1 : ℝ)) :
  IntervalIntegrable F (μ := volume) (X : ℝ) (X + k + 1 : ℝ) :=
  IntervalIntegrable.trans hL hR

/-- Coerção auxiliar: `↑X + (↑j + 1) = ↑X + ↑(j+1)`. -/
lemma cast_add_simpl (X j : ℕ) :
  (↑X + (↑j + 1) : ℝ) = (↑X + ↑(j + 1) : ℝ) := by
  rw [Nat.cast_add_one]

/-- Integrabilidade acumulada em `[X, X+k+1]` a partir de blocos. -/
lemma intervalIntegrable_blocks_aux
  (F : ℝ → ℝ) (X k : ℕ)
  (hint : ∀ n ≤ k,
    IntervalIntegrable F (μ := volume)
      (↑X + ↑n) (↑X + ↑n + 1)) :
  IntervalIntegrable F (μ := volume)
    (↑X) (↑X + ↑k + 1) := by
  induction' k with j ih
  · -- caso base
    simpa [add_zero, Nat.cast_zero] using hint 0 (by simp)
  · -- passo indutivo
    have hL := ih (by
      intro n hn
      exact hint n (Nat.le_trans hn (Nat.le_succ j)))
    have hR := hint (j + 1) (by simp)
    -- normaliza a borda direita de hL para casar com hR
    have eq_cast := cast_add_simpl X j
    rw [add_assoc] at hL
    rw [eq_cast] at hL
    exact IntervalIntegrable.trans hL hR

/-- Prefixo integrável: dos blocos até `k` obtemos `[X, X+k]`. -/
lemma prefix_integrable_of_hint
  (F : ℝ → ℝ) (X k : ℕ)
  (hint : ∀ n ≤ k,
    IntervalIntegrable F (μ := volume)
      (↑X + ↑n) (↑X + ↑n + 1)) :
  IntervalIntegrable F (μ := volume) (↑X) (↑X + ↑k) := by
  induction' k with j ih
  · simp
  ·
    -- acumula até [X, X+j]
    have hL : IntervalIntegrable F (μ := volume) (↑X) (↑X + ↑j) :=
      ih (by intro n hn; exact hint n (Nat.le_trans hn (Nat.le_succ _)))
    -- bloco intermediário [X+j, X+j+1]
    have hMid : IntervalIntegrable F (μ := volume) (↑X + ↑j) (↑X + ↑j + 1) :=
      hint j (Nat.le_succ j)
    -- concatena: [X, X+j] ⟶ [X, X+j+1]
    have hL' : IntervalIntegrable F (μ := volume) (↑X) (↑X + ↑j + 1) :=
      IntervalIntegrable.trans hL hMid
    -- ajusta a borda: ↑X + ↑j + 1 = ↑X + ↑(j+1)
    simpa [add_assoc, Nat.cast_add_one] using hL'


-- ######################################
-- ## 4) Decomposição global por blocos ##
-- ######################################

/-- Caso base: `Y = 1`. -/
lemma sum_blocks_eq_base
  (F : ℝ → ℝ) (X : ℕ)
  (_ : IntervalIntegrable F (μ := volume) (↑X) (↑X + 1)) :
  ∫ t in (↑X)..(↑X + 1), F t
    = Finset.sum (Finset.range 1)
        (fun n => blockIntegral F X n) := by
  simp [Finset.range_one, blockIntegral]

/-- Passo indutivo: adiciona o bloco `k`. -/
lemma sum_blocks_eq_step
  (F : ℝ → ℝ) (X k : ℕ)
  (ih : ∫ t in (↑X)..(↑X + ↑k), F t
          = Finset.sum (Finset.range k) (fun n => blockIntegral F X n))
  (hL : IntervalIntegrable F (μ := volume) (↑X) (↑X + ↑k))
  (hR : IntervalIntegrable F (μ := volume) (↑X + ↑k) (↑X + ↑k + 1)) :
  ∫ t in (↑X)..(↑X + ↑(k + 1)), F t
    = Finset.sum (Finset.range (k + 1)) (fun n => blockIntegral F X n) := by
  have hadd := integral_split_step F X k hL hR
  have eq₁ : ∫ t in (↑X)..(↑X + ↑(k + 1)), F t
      = (∫ t in (↑X)..(↑X + ↑k), F t) + blockIntegral F X k := by
    simpa [blockIntegral] using hadd
  calc
    ∫ t in (↑X)..(↑X + ↑(k + 1)), F t
      = (∫ t in (↑X)..(↑X + ↑k), F t) + blockIntegral F X k := eq₁
    _ = Finset.sum (Finset.range k) (fun n => blockIntegral F X n)
          + blockIntegral F X k := by rw [ih]
    _ = Finset.sum (Finset.range (k + 1)) (fun n => blockIntegral F X n) := by
        rw [Finset.sum_range_succ]

/-- Passo sucessor para `totalIntegral`: separa o bloco final. -/
lemma totalIntegral_succ
  (F : ℝ → ℝ) (X k : ℕ)
  (hL : IntervalIntegrable F (μ := volume) (↑X) (↑X + ↑k))
  (hR : IntervalIntegrable F (μ := volume) (↑X + ↑k) (↑X + ↑k + 1)) :
  totalIntegral F X (k + 1)
    = totalIntegral F X k + blockIntegral F X k := by
  -- compatibiliza `↑X + ↑(k+1)` com `↑X + (↑k + 1)`
  have eq_end : (↑X + ↑(k + 1) : ℝ) = (↑X + (↑k + 1) : ℝ) := by
    simp [Nat.cast_add_one]
  -- versão de aditividade no formato desejado
  have hadd' :
      ∫ t in (↑X)..(↑X + ↑(k + 1)), F t
        = (∫ t in (↑X)..(↑X + ↑k), F t)
          + (∫ t in (↑X + ↑k)..(↑X + ↑k + 1), F t) := by
    -- obtém a forma com `(↑k + 1)` e reescreve a borda com `eq_end`
    have hadd := integral_split_step F X k hL hR
    simpa [eq_end] using hadd
  simpa [totalIntegral, blockIntegral] using hadd'

/-- Soma de blocos: caso base `0`. -/
lemma blocksSum_zero (F : ℝ → ℝ) (X : ℕ) :
  blocksSum F X 0 = 0 := by
  simp [blocksSum]

/-- Soma de blocos: passo sucessor. -/
lemma blocksSum_succ (F : ℝ → ℝ) (X k : ℕ) :
  blocksSum F X (k + 1) = blocksSum F X k + blockIntegral F X k := by
  simp [blocksSum, Finset.sum_range_succ]

/-- Igualdade analítica: integral total é soma dos blocos. -/
lemma totalIntegral_blocks_eq
  (F : ℝ → ℝ) (X Y : ℕ)
  (hint : ∀ n < Y,
    IntervalIntegrable F (μ := volume)
      (↑X + ↑n) (↑X + ↑n + 1)) :
  totalIntegral F X Y = blocksSum F X Y := by
  induction' Y with k ih
  · simp [totalIntegral, blocksSum]
  · have hL := prefix_integrable_of_hint F X k (by
      intro n hn; exact hint n (Nat.lt_of_le_of_lt hn (Nat.lt_succ_self _)))
    have hR := hint k (Nat.lt_succ_self _)
    have step := totalIntegral_succ F X k hL hR
    rw [step, ih (by
      intro n hn; exact hint n (Nat.lt_trans hn (Nat.lt_succ_self _))), blocksSum_succ]


-- ###############################################
-- ## 5) Auxiliares de ordem/constância e álgebra ##
-- ###############################################

/-- Desigualdade simples: `↑X + ↑n < ↑X + ↑n + 1`. -/
lemma real_bounds (X n : ℕ) :
  (↑X + ↑n : ℝ) < (↑X + ↑n + 1 : ℝ) := by
  have h₁ : (0 : ℝ) < 1 := by norm_num
  have h₂ : (↑X + ↑n : ℝ) + 0 = (↑X + ↑n) := by simp
  have h₃ : (↑X + ↑n : ℝ) + 1 = (↑X + ↑n + 1) := by simp
  have h := add_lt_add_left h₁ (↑X + ↑n)
  rwa [h₂, h₃] at h

/-- `A_y` é constante em cada bloco unitário `[X + n, X + n + 1]`. -/
lemma Ay_const_on_block
  (A_y : ℕ → ℝ → ℝ)
  (y X n : ℕ)
  (hmono : ∀ (t₁ t₂ : ℝ),
    t₁ ∈ Set.Icc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ) →
    t₂ ∈ Set.Icc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ) →
    A_y y t₁ = A_y y t₂) :
  ∀ t ∈ Set.Icc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ),
    A_y y t = A_y y (↑X + ↑n : ℝ) := by
  intro t ht
  -- ponto esquerdo pertence a `Icc`
  have a_mem : (↑X + ↑n : ℝ) ∈ Set.Icc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ) := by
    refine ⟨le_rfl, ?_⟩
    have h01 : (0 : ℝ) ≤ 1 := by norm_num
    have : (↑X + ↑n : ℝ) ≤ ↑X + ↑n + 1 := by
      convert add_le_add_left h01 (↑X + ↑n : ℝ) using 1
      · simp [add_zero]
    exact this
  exact hmono t (↑X + ↑n : ℝ) ht a_mem

/-- Versão genérica: constância em `Icc a b` implica `f t = f a`. -/
lemma Ay_const_on_Icc
  (A_y : ℕ → ℝ → ℝ) (y : ℕ)
  {a b : ℝ}
  (hmono : ∀ {t₁ t₂ : ℝ},
    t₁ ∈ Set.Icc a b → t₂ ∈ Set.Icc a b →
    A_y y t₁ = A_y y t₂) :
  ∀ {t : ℝ}, t ∈ Set.Icc a b → A_y y t = A_y y a := by
  intro t ht
  have a_mem : a ∈ Set.Icc a b := ⟨le_rfl, le_trans ht.1 ht.2⟩
  exact hmono ht a_mem

/-- Distribuição de negação sobre soma finita. -/
lemma sum_neg_distrib' {α} [DecidableEq α]
  (s : Finset α) (f : α → ℝ) :
  Finset.sum s (fun a => - f a) = - Finset.sum s f := by
  simp [Finset.sum_neg_distrib]

/-- Troca de ordem na diferença. -/
lemma diff_flip (g : ℝ → ℝ) (x : ℝ) :
  g (x + 1) - g x = - (g x - g (x + 1)) := by
  ring

/-- Versão “pronta para uso” do Teorema Fundamental do Cálculo em um bloco:
    se `g'` é derivada de `g` em `uIcc a b` e é integrável, então `∫ g' = g b - g a`. -/
lemma FTC_on_block
  (g g' : ℝ → ℝ) {a b : ℝ}
  (hder : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t)
  (hint : IntervalIntegrable g' (μ := volume) a b) :
  ∫ t in a..b, g' t = g b - g a := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint

/-- Versão real ajustada do bloco unitário:
    se `A` é constante em `[a,b]` e `g'` é a derivada de `g`,
    então `∫ g' * A = A(a) * (g b - g a)`. -/
lemma block_integral_formula_real
  (g g' : ℝ → ℝ) (A : ℝ → ℝ)
  {a b : ℝ} (hle : a ≤ b)
  (hder : ∀ t ∈ Set.uIcc a b, HasDerivAt g (g' t) t)
  (hint : IntervalIntegrable g' (μ := volume) a b)
  (hconst : ∀ t ∈ Set.Icc a b, A t = A a) :
  ∫ t in a..b, g' t * A t = A a * (g b - g a) := by
  -- Regra fundamental do cálculo
  have hFTC : ∫ t in a..b, g' t = g b - g a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hder hint
  -- Igualdade pontual dentro do intervalo
  have h_eqon : EqOn (fun t => g' t * A t) (fun t => (A a) * g' t) (Set.uIcc a b) := by
    intro t ht
    have tIcc : t ∈ Set.Icc a b := by
      simp [Set.uIcc, hle] at ht
      exact ⟨ht.1, ht.2⟩
    simp [hconst t tIcc, mul_comm]
  have hrewrite := intervalIntegral.integral_congr (μ := volume) h_eqon
  -- Constante sai do integral
  have hscale :
      ∫ t in a..b, (A a) * g' t = (A a) * ∫ t in a..b, g' t := by
    exact intervalIntegral.integral_const_mul (μ := volume) (r := A a) (f := g')
  -- Encadeia as igualdades
  calc
    ∫ t in a..b, g' t * A t
        = ∫ t in a..b, (A a) * g' t := hrewrite
    _   = (A a) * ∫ t in a..b, g' t := hscale
    _   = (A a) * (g b - g a) := by rw [hFTC]

/-- Versão discreta especializada: integral em bloco unitário `[X+n, X+n+1]`. -/
lemma block_integral_formula_nat
  (g g' : ℝ → ℝ)
  (A_y : ℕ → ℝ → ℝ)
  (y X n : ℕ)
  (hder : ∀ t ∈ Set.uIcc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ), HasDerivAt g (g' t) t)
  (hint : IntervalIntegrable g' (μ := volume) (↑X + ↑n) (↑X + ↑n + 1))
  (hconst : ∀ t ∈ Set.Icc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ),
              A_y y t = A_y y (↑X + ↑n : ℝ)) :
  ∫ t in (↑X + ↑n)..(↑X + ↑n + 1), g' t * A_y y t
    = A_y y (↑X + ↑n : ℝ) * (g (↑X + ↑n + 1) - g (↑X + ↑n)) := by
  -- aplica a versão real do lema
  apply block_integral_formula_real
  · -- a ≤ b no bloco [X+n, X+n+1]
    exact le_of_lt (real_bounds X n)
  · -- derivada em uIcc
    intro t ht; exact hder t ht
  · -- integrabilidade de g' no bloco
    exact hint
  · -- constância de A_y no bloco
    intro t ht; exact hconst t ht

/-- Fórmula de decomposição de Abel:
    o integral de `g' * A_y y` em `[X, X+Y]` se expressa como
    a soma dos blocos unitários. -/
lemma abel_block_partition_neg
  (g g' : ℝ → ℝ)
  (A_y : ℕ → ℝ → ℝ)
  (X Y y : ℕ)
  (_hX : 1 ≤ X) (_hY : 1 ≤ Y) (_hy : 2 ≤ y)
  (hder : ∀ n < Y, ∀ t ∈ Set.uIcc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ),
            HasDerivAt g (g' t) t)
  (hint : ∀ n < Y,
            IntervalIntegrable g' (μ := volume)
              (↑X + ↑n) (↑X + ↑n + 1))
  (hconst : ∀ n < Y,
              ∀ t ∈ Set.Icc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ),
                A_y y t = A_y y (↑X + ↑n : ℝ)) :
  ∫ t in (↑X)..(↑X + ↑Y), g' t * A_y y t
    =
  Finset.sum (Finset.range Y)
      (fun n =>
        (A_y y (↑X + ↑n : ℝ))
          * (g (↑X + ↑n + 1 : ℝ) - g (↑X + ↑n : ℝ))) := by
  classical
  --------------------------------------------------------------------------------
  -- 1) Integrabilidade do produto em cada bloco (via AE em Ι = Ioc)
  --------------------------------------------------------------------------------
  have hint_prod :
    ∀ n < Y,
      IntervalIntegrable (fun t => g' t * A_y y t) (μ := volume)
        (↑X + ↑n) (↑X + ↑n + 1) := by
    intro n hn
    -- integrável: constante * g'
    have hG :
        IntervalIntegrable (fun t => (A_y y (↑X + ↑n : ℝ)) * g' t) (μ := volume)
          (↑X + ↑n) (↑X + ↑n + 1) :=
      (hint n hn).const_mul (A_y y (↑X + ↑n : ℝ))
    -- no bloco, A_y é constante ⇒ funções coincidem a.e. em Ι (Ioc)
    have hEqAE :
      (fun t => (A_y y (↑X + ↑n : ℝ)) * g' t)
        =ᶠ[ae (volume.restrict (Ι (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ)))]
        (fun t => g' t * A_y y t) := by
      -- ht : t ∈ Ι …  (mesmo conjunto que Ioc)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      -- converte explicitamente para Set.Ioc para usar o lema de inclusão
      have htIoc : t ∈ Set.Ioc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ) := by
        -- aqui o `simpa` usa que Ι é notação para Set.Ioc
        simpa using ht
      have htIcc :
          t ∈ Set.Icc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ) :=
        Set.Ioc_subset_Icc_self htIoc
      have hconst' : A_y y t = A_y y (↑X + ↑n : ℝ) := by
        simpa using hconst n hn t htIcc
      simp [hconst', mul_comm]
    -- converte o filtro Ι em uIoc (orientação canônica)
    have hle : (↑X + ↑n : ℝ) ≤ ↑X + ↑n + 1 := by
      have hNat : X + n ≤ X + n + 1 := Nat.le_succ (X + n)
      exact_mod_cast hNat
    have hEqAE_uIoc :
        (fun t => (A_y y (↑X + ↑n : ℝ)) * g' t)
          =ᶠ[ae (volume.restrict (Set.uIoc (↑X + ↑n : ℝ) (↑X + ↑n + 1 : ℝ)))]
          (fun t => g' t * A_y y t) := by
      simpa [Set.uIoc_of_le hle] using hEqAE
    exact IntervalIntegrable.congr (μ := volume) hG hEqAE_uIoc

  --------------------------------------------------------------------------------
  -- 2) Integral total como soma dos blocos
  --------------------------------------------------------------------------------
  have hsplit' :
    ∫ t in (↑X)..(↑X + ↑Y), g' t * A_y y t
      =
    Finset.sum (Finset.range Y)
      (fun n =>
        ∫ t in (↑X + ↑n)..(↑X + ↑n + 1), g' t * A_y y t) := by
    simpa [totalIntegral, blocksSum] using
      (totalIntegral_blocks_eq (fun t => g' t * A_y y t) X Y
        (by intro n hn; exact hint_prod n hn))

  --------------------------------------------------------------------------------
  -- 3) Fórmula local em cada bloco
  --------------------------------------------------------------------------------
  have hterm :
    ∀ n, n < Y →
      ∫ t in (↑X + ↑n)..(↑X + ↑n + 1), g' t * A_y y t
        = A_y y (↑X + ↑n : ℝ)
            * (g (↑X + ↑n + 1 : ℝ) - g (↑X + ↑n : ℝ)) := by
    intro n hn
    exact block_integral_formula_nat g g' A_y y X n
      (hder n hn) (hint n hn) (hconst n hn)

  have hmap :
    Finset.sum (Finset.range Y)
      (fun n =>
        ∫ t in (↑X + ↑n)..(↑X + ↑n + 1), g' t * A_y y t)
      =
    Finset.sum (Finset.range Y)
      (fun n =>
        A_y y (↑X + ↑n : ℝ)
          * (g (↑X + ↑n + 1 : ℝ) - g (↑X + ↑n : ℝ))) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn' : n < Y := Finset.mem_range.mp hn
    simpa using hterm n hn'

  --------------------------------------------------------------------------------
  -- 4) Encadeamento final
  --------------------------------------------------------------------------------
  calc
    ∫ t in (↑X)..(↑X + ↑Y), g' t * A_y y t
        = Finset.sum (Finset.range Y)
            (fun n =>
              ∫ t in (↑X + ↑n)..(↑X + ↑n + 1),
                g' t * A_y y t) := hsplit'
    _   = Finset.sum (Finset.range Y)
            (fun n =>
              A_y y (↑X + ↑n : ℝ)
                * (g (↑X + ↑n + 1 : ℝ) - g (↑X + ↑n : ℝ))) := hmap


  #print axioms abel_block_partition_neg
  #check abel_block_partition_neg
