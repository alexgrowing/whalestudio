import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff

open scoped Pointwise

namespace GlobalTheory.ValuationOfMemIff

theorem le_iff_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (x y : Ω) :
    A.valuation (σ x) ≤ A.valuation (σ y) ↔ A.valuation x ≤ A.valuation y := by
  by_cases hy : y = 0
  · subst hy
    simp
  · have hσy : σ y ≠ 0 := by simpa using hy
    have key : ∀ a b : Ω, b ≠ 0 → (A.valuation a ≤ A.valuation b ↔ a / b ∈ A) := by
      intro a b hb
      rw [← A.valuation_le_one_iff, map_div₀,
        div_le_one₀ (by simpa [pos_iff_ne_zero] using hb)]
    rw [key _ _ hσy, key _ _ hy, ← map_div₀, h]

theorem not_injective_pow {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (σ : Ω ≃ₐ[E] Ω) (t : Ω) (ht : IsIntegral E t) :
    ¬ Function.Injective (fun k : ℕ => (σ ^ k) t) := by
  intro hinj

  have hsub : Set.range (fun k : ℕ => (σ ^ k) t) ⊆ (minpoly E t).rootSet Ω := by
    rintro _ ⟨k, rfl⟩
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero ht, ?_⟩
    have := Polynomial.aeval_algHom_apply ((σ ^ k : Ω ≃ₐ[E] Ω) : Ω →ₐ[E] Ω) t (minpoly E t)
    simpa [minpoly.aeval] using this
  exact Set.infinite_range_of_injective hinj (((minpoly E t).rootSet_finite Ω).subset hsub)

theorem valuation_eq_of_mem_iff {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : Ω ≃ₐ[E] Ω) (h : ∀ x, σ x ∈ A ↔ x ∈ A) (t : Ω)
    (ht : IsIntegral E t) : A.valuation (σ t) = A.valuation t := by
  have hsucc : ∀ k : ℕ, (σ ^ (k + 1)) t = σ ((σ ^ k) t) := fun k => by
    rw [pow_succ', AlgEquiv.mul_apply]

  have hlt : ∀ x y : Ω, A.valuation (σ x) < A.valuation (σ y) ↔ A.valuation x < A.valuation y := by
    intro x y
    rw [lt_iff_not_ge, lt_iff_not_ge, le_iff_of_mem_iff A σ h]
  have hinj : ∀ w : ℕ → _, (StrictMono w ∨ StrictAnti w) →
      (∀ k, w k = A.valuation ((σ ^ k) t)) → False := by
    intro w hw hwk
    apply not_injective_pow σ t ht
    intro a b hab
    have : w a = w b := by rw [hwk, hwk]; exact congrArg A.valuation hab
    rcases hw with hw | hw
    · exact hw.injective this
    · exact hw.injective this
  rcases lt_trichotomy (A.valuation (σ t)) (A.valuation t) with hc | hc | hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inr (strictAnti_nat_of_succ_lt ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih
  · exact hc
  · exfalso
    refine hinj (fun k => A.valuation ((σ ^ k) t)) (Or.inl (strictMono_nat_of_lt_succ ?_)) fun _ => rfl
    intro k
    induction k with
    | zero => simpa using hc
    | succ k ih =>
      rw [hsucc (k + 1), hsucc k]
      rw [hsucc k] at ih
      exact (hlt _ _).2 ih

theorem valuation_apply_eq : ∀ (E Ω : Type) [inst : Field E] [NumberField E] [inst_2 : Field Ω] [inst_3 : Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (σ : Formalism.ConjugateSelfDual.G E Ω), Membership.mem (ReciprocityTheory.Gal.Dec A) σ → ∀ (t : Ω), Eq ((ValuationSubring.valuation A) (σ t)) ((ValuationSubring.valuation A) t) := by
  intro E Ω _ _ _ _ _ A σ hσ t
  have halg : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  exact valuation_eq_of_mem_iff A σ (ReciprocityTheory.Gal.apply_mem_iff_of_mem_Dec hσ) t
    (Algebra.IsIntegral.isIntegral t)

end GlobalTheory.ValuationOfMemIff
