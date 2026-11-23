import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterGoodF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsOrbitCompNonvanish
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem OrbitCompNonvanish.isHomogeneous_blkWt {P : Ideal (MRing ι)} (hP : IsMultiHomogIdeal P) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  apply Ideal.homogeneous_span
  intro f hf
  obtain ⟨a, ha⟩ := hS f hf
  refine ⟨Finsupp.equivFunOnFinite.symm a, (mem_weightedHomogeneousSubmodule ℤ _ _ _).mpr ?_⟩
  intro m hm
  ext k
  rw [weight_blkWt_apply, ha m (mem_support_iff.mpr hm) k]
  simp

theorem OrbitCompNonvanish.isMultiHomog_component (E : MRing ι) (δ : K →₀ ℕ) :
    IsMultiHomog (weightedHomogeneousComponent (blkWt (ι := ι)) δ E) δ := by
  intro m hm k
  have h := weightedHomogeneousComponent_isWeightedHomogeneous (w := blkWt (ι := ι)) δ E
    (mem_support_iff.mp hm)
  rw [← weight_blkWt_apply, h]

theorem OrbitCompNonvanish.proof : OrbitCompNonvanish.Statement := by
  intro K _ ι _ P E hP hE
  classical
  have hPh := OrbitCompNonvanish.isHomogeneous_blkWt hP
  obtain ⟨δ, hδ⟩ : ∃ δ, weightedHomogeneousComponent (blkWt (ι := ι)) δ E ∉ P := by
    by_contra h
    push Not at h
    exact hE ((mem_iff_weightedHomogeneousComponent_mem ℤ _ hPh E).mpr h)
  refine ⟨_, δ, OrbitCompNonvanish.isMultiHomog_component E δ, hδ, fun z hz => ?_⟩

  let comp : (K →₀ ℕ) → MRing ι := fun b => weightedHomogeneousComponent (blkWt (ι := ι)) b E
  let lam : (K →₀ ℕ) → ℂ := fun b => eval z (map (Int.castRingHom ℂ) (comp b))
  have hfin := weightedHomogeneousComponent_finsupp (w := blkWt (ι := ι)) E
  let T : Finset (K →₀ ℕ) := insert δ hfin.toFinset
  have hsum : ∑ b ∈ T, comp b = E := by
    rw [← Finset.sum_subset (Finset.subset_insert δ hfin.toFinset), ← finsum_eq_sum _ hfin]
    · exact sum_weightedHomogeneousComponent _ E
    · intro b _ hb
      by_contra hne
      exact hb (hfin.mem_toFinset.mpr hne)
  let Q : MvPolynomial K ℂ := ∑ b ∈ T, monomial b (lam b)
  have hQ : ∀ c : K → ℂ, eval c Q = eval (fun p => c p.1 * z p) (map (Int.castRingHom ℂ) E) := by
    intro c
    conv_rhs => rw [← hsum]
    simp only [Q, map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [eval_smul_homog (comp b) b (OrbitCompNonvanish.isMultiHomog_component E b) c z, eval_monomial,
      Finsupp.prod_fintype _ _ (by simp)]
    ring
  have hQ0 : Q ≠ 0 := by
    intro h0
    have hc := congrArg (coeff δ) h0
    simp only [Q, coeff_sum, coeff_monomial, coeff_zero] at hc
    rw [Finset.sum_ite_eq' T δ, if_pos (Finset.mem_insert_self _ _)] at hc
    exact hz hc
  by_contra hno
  push Not at hno
  apply hQ0
  refine funext_set (fun _ => ({0}ᶜ : Set ℂ)) (fun _ => (Set.finite_singleton 0).infinite_compl)
    fun x hx => ?_
  rw [hQ, map_zero]
  exact hno x fun k => hx k (Set.mem_univ k)

end GroundTheory.Heights₂.Heights.Inter
