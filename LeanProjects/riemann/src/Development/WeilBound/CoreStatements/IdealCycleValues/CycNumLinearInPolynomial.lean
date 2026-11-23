import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.cycNum_linear_in_polynomial : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (Z : Ideal (MRing ι O) → ℤ) (cls : σ → K → ℤ) (Q : List (K → ℤ)), (∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q) ∧ (∀ (c : ℝ) (H : MvPolynomial σ ℝ), cycNum Z cls (C c * H) Q = c * cycNum Z cls H Q) ∧ (∀ (α : Type) (s : Finset α) (H : α → MvPolynomial σ ℝ), cycNum Z cls (∑ a ∈ s, H a) Q = ∑ a ∈ s, cycNum Z cls (H a) Q) ∧ ∀ (μ : σ →₀ ℕ) (c : ℝ), cycNum Z cls (monomial μ c) Q = c * (cycList Z (classList cls μ ++ Q) : ℝ) := by
  intro O _ _ _ K _ _ ι _ σ Z cls Q
  classical
  set g : (σ →₀ ℕ) → ℝ := fun μ => (cycList Z (classList cls μ ++ Q) : ℝ) with hg
  have key : ∀ (H : MvPolynomial σ ℝ) (s : Finset (σ →₀ ℕ)), H.support ⊆ s →
      cycNum Z cls H Q = ∑ μ ∈ s, MvPolynomial.coeff μ H * g μ := by
    intro H s hs
    show ∑ μ ∈ H.support, MvPolynomial.coeff μ H * g μ = _
    refine Finset.sum_subset hs (fun μ _ hμ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hμ, zero_mul]
  have hadd : ∀ H H' : MvPolynomial σ ℝ, cycNum Z cls (H + H') Q = cycNum Z cls H Q + cycNum Z cls H' Q := by
    intro H H'
    rw [key (H + H') (H.support ∪ H'.support) MvPolynomial.support_add,
      key H (H.support ∪ H'.support) Finset.subset_union_left,
      key H' (H.support ∪ H'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : cycNum Z cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 ∅ (by simp)]
    simp
  refine ⟨hadd, ?_, ?_, ?_⟩
  · intro c H
    have hs : (MvPolynomial.C c * H).support ⊆ H.support := by
      intro μ hμ
      rw [MvPolynomial.mem_support_iff] at hμ ⊢
      rw [MvPolynomial.coeff_C_mul] at hμ
      exact right_ne_zero_of_mul hμ
    rw [key _ H.support hs, key H H.support subset_rfl, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_C_mul, mul_assoc]
  · intro α s H
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  · intro μ c
    rw [key _ {μ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
