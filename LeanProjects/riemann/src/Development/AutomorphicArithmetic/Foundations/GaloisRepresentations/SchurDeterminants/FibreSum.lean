import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SchurDeterminants.SchurYOffClr

noncomputable section

open Finset
open scoped Classical

namespace UpperTheory.Gal.Schur

def FibreSum : Prop :=
  ∀ (E K : Type) [Field E] [NumberField E] [Field K] [CharZero K] (n : ℕ)
    (lam : (E →+* K) → Fin n → ℕ), ∃ k₀, ∀ k, k₀ ≤ k →
    ∀ (N : NumberField.RingOfIntegers E), N ≠ 0 → ∀ B : Finset K,
      ∃ c : (Fin k → NumberField.RingOfIntegers E) →₀ K,
        (∀ α ∈ c.support, ∀ s, α s ≠ 0 ∧ N ∣ α s ∧ ∀ τ : E →+* K, ∀ b ∈ B, 1 - resO τ (α s) * b ≠ 0) ∧
        ∀ (R : Type) [CommRing R] [Algebra K R] [Algebra ℚ R] (t₀ t₁ : E →+* K), t₀ ≠ t₁ →
          ∀ (ε : (E →+* K) → ℕ) (m : ℕ) (g : (E →+* K) → Fin n → R) (y : R),
          ((∀ i, lam t₁ i = m) → (∀ i j, j ≠ i → IsUnit (g t₀ j - g t₀ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₀ j - y * g t₀ i) * Ring.inverse (g t₀ j - g t₀ i))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ ((n - 1) * m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (lam t₀ i + (n - 1 - (i : ℕ))))) ∧
          ((∀ i, lam t₀ i = m) → (∀ i j, j ≠ i → IsUnit (g t₁ j - g t₁ i)) →
            (c.sum fun α r => r • ∑ i,
              (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) *
                ∏ j ∈ univ.erase i, ((g t₁ i - y * g t₁ j) * Ring.inverse (g t₁ i - g t₁ j))) =
            (∏ τ, sch (lam τ) (g τ)) *
              (y ^ (m + ∑ τ ∈ (univ.erase t₀).erase t₁, ε τ * ∑ i, lam τ i) *
                ∑ i : Fin n, y ^ (∑ j ∈ univ.erase i, lam t₁ j + (i : ℕ))))

theorem fibreSum_of (h : InterpNF) (h₁ : Fibre) (h₂ : FibreOff) : FibreSum := by
  intro E K _ _ _ _ n lam
  obtain ⟨k₀, hk⟩ := h E K n lam
  refine ⟨k₀, fun k hk' N hN B => ?_⟩
  obtain ⟨c, hc, hsum⟩ := hk k hk' N hN B
  refine ⟨c, hc, fun R _ _ _ t₀ t₁ ht ε m g y => ?_⟩
  have swap : ∀ C : Fin n → R,
      (c.sum fun α r => r • ∑ i,
        (∏ τ, ∏ s, detOne (algebraMap K R (resO τ (α s))) (twist t₀ t₁ ε y i g τ)) * C i) =
      ∑ i, (∏ τ, sch (lam τ) (twist t₀ t₁ ε y i g τ)) * C i := by
    intro C
    rw [Finsupp.sum]
    simp_rw [Finset.smul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hsum R (twist t₀ t₁ ε y i g), Finsupp.sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [smul_mul_assoc]
  refine ⟨fun hm hu => ?_, fun hm hu => ?_⟩
  · rw [swap]
    exact h₁ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu
  · rw [swap]
    exact h₂ R (E →+* K) n t₀ t₁ ht ε lam m hm g y hu

end UpperTheory.Gal.Schur
