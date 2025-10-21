/-
  RoughBlocks.Light.B2Support
  Suporte mínimo (Prop) para a faixa finita:
  - InBlock / NoSmallPrime
  - lemas para subir de "todos fatores > m" ⇒ NoSmallPrime
-/
import Mathlib

namespace RoughBlocks
namespace Light

/-- `InBlock m x n` significa que `n ∈ {m^2+xm+1, …, m^2+(x+1)m}`. -/
def InBlock (m x n : Nat) : Prop :=
  ∃ k : Nat, 1 ≤ k ∧ k ≤ m ∧ n = m*m + x*m + k

/-- `NoSmallPrime m n` significa: nenhum primo `q ≤ m` divide `n`. -/
def NoSmallPrime (m n : Nat) : Prop :=
  ∀ {q : Nat}, Nat.Prime q → q ≤ m → ¬ q ∣ n

/-- Se `n = m^2 + x m + k` com `1 ≤ k ≤ m`, então `InBlock m x n`. -/
lemma inBlock_of_offset {m x n k : Nat}
    (hk1 : 1 ≤ k) (hk2 : k ≤ m)
    (hn : n = m*m + x*m + k) : InBlock m x n := by
  refine ⟨k, hk1, hk2, ?_⟩
  simpa [hn]

/-! ### Lemas “fatores > m” ⇒ `NoSmallPrime m n` -/

/-- Se `q` é primo, `q ≤ m < p` e `p` é primo, então `q ∤ p^e`. -/
lemma prime_not_dvd_pow_of_lt
    {q p m e : Nat}
    (hq : Nat.Prime q) (hle : q ≤ m) (hlt : m < p) (hp : Nat.Prime p) :
    ¬ q ∣ p ^ e := by
  intro hqp_pow
  -- de q ∣ p^e obtemos q ∣ p
  have hqp : q ∣ p := hq.dvd_of_dvd_pow hqp_pow
  -- como p é primo, q ∣ p implica q = 1 ∨ q = p
  have hcases : q = 1 ∨ q = p := (Nat.dvd_prime hp).1 hqp
  -- mas q ≠ 1 e também q < p (pois q ≤ m < p)
  have hq_ne_one : q ≠ 1 := hq.ne_one
  have hq_lt_p : q < p := lt_of_le_of_lt hle hlt
  cases hcases with
  | inl h1 => exact (hq_ne_one h1).elim
  | inr hqeqp => exact (ne_of_lt hq_lt_p) hqeqp

/-- Auxiliar (simples): para `f acc (p,e) := acc * p^e`,
    `foldl f a tl = a * foldl f 1 tl`. -/
private lemma foldl_mul_pows_eq_seed
    (a : Nat) (tl : List (Nat × Nat)) :
    List.foldl (fun acc (pe : Nat × Nat) => acc * pe.1 ^ pe.2) a tl
  = a * List.foldl (fun acc (pe : Nat × Nat) => acc * pe.1 ^ pe.2) 1 tl := by
  induction tl generalizing a with
  | nil =>
      simp
  | cons pe tl ih =>
      rcases pe with ⟨p, e⟩
      -- reduce using the `foldl` cons equation
      simp [List.foldl_cons]
      -- apply the induction hypothesis to both seeds we need to relate
      have h1 := ih (a := a * p ^ e)
      have h2 := ih (a := p ^ e)
      -- rewrite both sides using the IH results, leaving a trivial associativity
      rw [h1, h2]
      simp [Nat.mul_assoc]

/-- Produto de potências de fatores com `p > m` não tem divisor primo `q ≤ m`. -/
lemma noSmallPrime_of_arrayFactors_gt
    (m : Nat)
    (facts : List (Nat × Nat))  -- lista de (p, e)
    (hpr : ∀ (p e), (p, e) ∈ facts → Nat.Prime p)
    (hgt : ∀ (p e), (p, e) ∈ facts → m < p) :
    NoSmallPrime m (facts.foldl (fun acc (pe : Nat × Nat) => acc * pe.1 ^ pe.2) 1) := by
  -- defina o produto uma vez para facilitar a indução
  let prod : List (Nat × Nat) → Nat :=
    fun L => L.foldl (fun acc (pe : Nat × Nat) => acc * pe.1 ^ pe.2) 1
  -- indução na lista de fatores
  induction facts with
  | nil =>
      -- n = 1: nenhum primo ≤ m divide 1
      intro q hq _ hdiv
      have : q = 1 := Nat.dvd_one.mp hdiv
      exact (hq.ne_one this).elim
  | cons pe tl ih =>
      rcases pe with ⟨p, e⟩
      have hp : Nat.Prime p := hpr p e (by simp)
      have hmp : m < p := hgt p e (by simp)
      -- restrinja as hipóteses à cauda tl (para aplicar `ih`)
      have hpr_tl : ∀ p e, (p, e) ∈ tl → Nat.Prime p := by
        intro p' e' hin
        exact hpr p' e' (by simpa [hin])
      have hgt_tl : ∀ p e, (p, e) ∈ tl → m < p := by
        intro p' e' hin
        exact hgt p' e' (by simpa [hin])
      have ihNS : NoSmallPrime m (prod tl) := ih hpr_tl hgt_tl
      -- objetivo: para todo q primo ≤ m, ¬ q ∣ (p^e * prod tl)
      intro q hq hqle hdiv
      -- reescreve foldl na cabeça: `foldl f 1 ((p,e)::tl) = (p^e) * prod tl`
      have hfold_cons :
        List.foldl (fun acc (pe : Nat × Nat) => acc * pe.1 ^ pe.2) 1 ((p, e) :: tl)
          = (p ^ e) * (prod tl) := by
        -- primeiro, põe a semente 1 na cabeça: vira semente (p^e) na cauda
        have h := foldl_mul_pows_eq_seed (a := p ^ e) (tl := tl)
        -- `h : foldl f (p^e) tl = (p^e) * foldl f 1 tl`
        -- mas `foldl f 1 ((p,e)::tl) = foldl f (1 * p^e) tl = foldl f (p^e) tl`
        simpa [prod, List.foldl_cons, Nat.one_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      have hcases : q ∣ p ^ e ∨ q ∣ prod tl :=
        (Nat.Prime.dvd_mul hq).1 (by simpa [hfold_cons] using hdiv)
      cases hcases with
      | inl hqdiv_pow =>
          exact (prime_not_dvd_pow_of_lt (q:=q) (p:=p) (m:=m) (e:=e)
            hq hqle hmp hp) hqdiv_pow
      | inr hqdiv_tl =>
          -- aplica NoSmallPrime na cauda
          exact ihNS hq hqle hqdiv_tl

end Light
end RoughBlocks
