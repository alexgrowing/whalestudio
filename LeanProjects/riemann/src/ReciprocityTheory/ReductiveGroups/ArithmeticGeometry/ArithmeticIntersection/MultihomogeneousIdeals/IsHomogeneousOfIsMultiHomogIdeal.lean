import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.CurveFilt

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.AI.I1

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*} [Field F]

def formsDeg (F : Type*) [Field F] (ι : K → Type*) [∀ k, Fintype (ι k)] (d : K → ℕ) :
    Submodule F (MRingOver F ι) :=
  Submodule.span F {f | ∃ m : (Σ k, ι k) →₀ ℕ, (∀ k, ∑ i, m ⟨k, i⟩ = d k) ∧ f = monomial m 1}

def hilbFn (J : Ideal (MRingOver F ι)) (d : K → ℕ) : ℕ :=
  Module.finrank F ((formsDeg F ι d).map (Ideal.Quotient.mkₐ F J).toLinearMap)

instance finiteDimensional_formsDeg (d : K → ℕ) : FiniteDimensional F (formsDeg F ι d) := by
  classical
  unfold formsDeg
  apply FiniteDimensional.span_of_finite
  have hfin : {m : (Σ k, ι k) →₀ ℕ | ∀ k, ∑ i, m ⟨k, i⟩ = d k}.Finite := by
    apply (Set.finite_Iic (Finsupp.equivFunOnFinite.symm fun p : Σ k, ι k => d p.1)).subset
    intro m hm
    rw [Set.mem_Iic, Finsupp.le_def]
    intro p
    simp only [Finsupp.equivFunOnFinite_symm_apply_apply]
    rw [← hm p.1]
    exact Finset.single_le_sum (f := fun i => m ⟨p.1, i⟩) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ p.2)
  exact (hfin.image fun m => monomial m (1 : F)).subset (by
    rintro f ⟨m, hm, rfl⟩
    exact ⟨m, hm, rfl⟩)

attribute [local instance] MvPolynomial.weightedGradedAlgebra

section SupSpan

variable [DecidableEq K]

end SupSpan

end ReciprocityTheory.ChartRestriction.G.AI.I1
