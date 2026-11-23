import Mathlib
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.BundleChernComparison
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.StatementsFlagIndependence
import Development.WeilBound.CoreStatements.IdealCycleValues.ProdMapToMultiset
import Development.WeilBound.CoreStatements.IdealCycleValues.IntersectionNumbersPermInvariant

open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

theorem BaseChangeColon.genNum_mul_expansion : ∀ (F : Type) [Field F] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (σ : Type) (V : Ideal (MRing ι F)) (cls : σ → K → ℤ) (H G : MvPolynomial σ ℝ) (Q : List (K → ℤ)), genNum F V cls (H * G) Q = ∑ μ ∈ G.support, G.coeff μ * genNum F V cls H (classList cls μ ++ Q) := by
  intro F _ K _ _ ι _ σ V cls H G Q
  classical
  have key : ∀ (P : MvPolynomial σ ℝ) (L : List (K → ℤ)) (s : Finset (σ →₀ ℕ)), P.support ⊆ s →
      genNum F V cls P L = ∑ κ ∈ s, MvPolynomial.coeff κ P * (intNumL F V (classList cls κ ++ L) : ℝ) := by
    intro P L s hs
    show ∑ κ ∈ P.support, MvPolynomial.coeff κ P * (intNumL F V (classList cls κ ++ L) : ℝ) = _
    refine Finset.sum_subset hs (fun κ _ hκ => ?_)
    rw [MvPolynomial.notMem_support_iff.mp hκ, zero_mul]
  have hadd : ∀ P P' : MvPolynomial σ ℝ, genNum F V cls (P + P') Q = genNum F V cls P Q + genNum F V cls P' Q := by
    intro P P'
    rw [key (P + P') Q (P.support ∪ P'.support) MvPolynomial.support_add,
      key P Q (P.support ∪ P'.support) Finset.subset_union_left,
      key P' Q (P.support ∪ P'.support) Finset.subset_union_right, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun _ _ => ?_)
    rw [MvPolynomial.coeff_add, add_mul]
  have hzero : genNum F V cls (0 : MvPolynomial σ ℝ) Q = 0 := by
    rw [key 0 Q ∅ (by simp)]
    simp
  have hsum : ∀ (α : Type) (s : Finset α) (P : α → MvPolynomial σ ℝ),
      genNum F V cls (∑ a ∈ s, P a) Q = ∑ a ∈ s, genNum F V cls (P a) Q := by
    intro α s P
    induction s using Finset.induction_on with
    | empty => simp [hzero]
    | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hadd, ih]
  have hmon : ∀ (κ : σ →₀ ℕ) (c : ℝ), genNum F V cls (monomial κ c) Q = c * (intNumL F V (classList cls κ ++ Q) : ℝ) := by
    intro κ c
    rw [key _ Q {κ} MvPolynomial.support_monomial_subset, Finset.sum_singleton,
      MvPolynomial.coeff_monomial, if_pos rfl]
  have hperm : ∀ ν μ : σ →₀ ℕ, intNumL F V (classList cls (ν + μ) ++ Q) = intNumL F V (classList cls ν ++ (classList cls μ ++ Q)) := by
    intro ν μ
    have hp : (classList cls (ν + μ)).Perm (classList cls ν ++ classList cls μ) := by
      rw [← Multiset.coe_eq_coe, ← Multiset.coe_add]
      simp only [classList, Multiset.coe_toList, Finsupp.toMultiset_add, Multiset.map_add]
    rw [← List.append_assoc]
    exact BaseChangeColon.intersection_numbers_perm_invariant.1 F K ι V _ _ (hp.append_right Q)
  conv_lhs => rw [H.as_sum, G.as_sum, Finset.sum_mul_sum]
  rw [hsum]
  simp_rw [hsum, MvPolynomial.monomial_mul, hmon]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun μ _ => ?_)
  rw [key H (classList cls μ ++ Q) H.support subset_rfl, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ν _ => ?_)
  rw [hperm]
  ring
