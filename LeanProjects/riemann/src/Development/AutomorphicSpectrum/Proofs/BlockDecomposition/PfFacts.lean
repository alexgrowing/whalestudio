import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.WittExactSequences.IsCompl

open TensorProduct CrystallineSemistableComparison.D
open scoped LaurentPolynomial

namespace GlobalTheory.CompanionTheory.PerfectRing

theorem pf_facts : ∀ (p : ℕ) [Fact p.Prime] (A : Type) [CommRing A], Pf p A →
    (∃ F : A ≃+* A, ∀ x, F x = x ^ p) ∧ (∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0) ∧
    (∀ (k : ℕ) (x : A), ∃ y, y ^ p ^ k = x) ∧ (∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y) ∧
    ∀ r : ℕ → A, IsRt p r → (∀ k, ∃ c, r k = c * r (k + 1) * r (k + 1)) ∧ (∀ k, r k ^ p ^ k = r 0) ∧
      ∀ (N : ℕ) (x : A), r 0 ^ N * x = 0 → ∀ k, r k * x = 0 := by
  intro p _ A _ h
  have hp : p.Prime := Fact.out
  have hadd : ∀ x y : A, (x + y) ^ p = x ^ p + y ^ p := by
    intro x y
    obtain ⟨c, hc⟩ := exists_add_pow_prime_eq hp x y
    rw [hc, h.char]
    simp
  let F : A →+* A :=
    { toFun := fun x => x ^ p
      map_one' := one_pow p
      map_mul' := fun x y => mul_pow x y p
      map_zero' := zero_pow hp.ne_zero
      map_add' := hadd }
  have hk : ∀ k : ℕ, Function.Bijective fun x : A => x ^ p ^ k := by
    intro k
    induction k with
    | zero =>
      simp only [pow_zero, pow_one]
      exact Function.bijective_id
    | succ k ih =>
      have : (fun x : A => x ^ p ^ (k + 1)) = (fun x : A => x ^ p) ∘ (fun x : A => x ^ p ^ k) := by
        funext x
        simp only [Function.comp_apply]
        rw [pow_succ, pow_mul]
      rw [this]
      exact h.bij.comp ih
  have hinj : ∀ (k : ℕ) (x y : A), x ^ p ^ k = y ^ p ^ k → x = y := fun k x y e => (hk k).1 e
  have hred : ∀ (x : A) (n : ℕ), x ^ n = 0 → x = 0 := by
    intro x n e
    apply hinj n
    have hlt : n < p ^ n := Nat.lt_pow_self hp.one_lt
    rw [pow_eq_zero_of_le hlt.le e, zero_pow (pow_ne_zero n hp.ne_zero)]
  refine ⟨⟨RingEquiv.ofBijective F h.bij, fun x => rfl⟩, hred, fun k x => (hk k).2 x, hinj, ?_⟩
  intro r hr
  have hroot : ∀ k, r k ^ p ^ k = r 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, hr k, ih]
  refine ⟨?_, hroot, ?_⟩
  · intro k
    refine ⟨r (k + 1) ^ (p - 2), ?_⟩
    have h2 : p = (p - 2) + 1 + 1 := by have := hp.two_le; omega
    conv_lhs => rw [← hr k, h2]
    rw [pow_succ, pow_succ]
  · intro N x e k
    apply hred _ (p ^ k * N + 1)
    calc (r k * x) ^ (p ^ k * N + 1)
        = r k ^ (p ^ k * N + 1) * x ^ (p ^ k * N + 1) := mul_pow _ _ _
      _ = r k * x ^ (p ^ k * N) * (r 0 ^ N * x) := by
          rw [pow_succ (r k), pow_mul, hroot k, pow_succ x]
          ring
      _ = 0 := by rw [e, mul_zero]

end GlobalTheory.CompanionTheory.PerfectRing
