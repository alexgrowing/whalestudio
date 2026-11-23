import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsIntersectionFamily
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Bridge

open MvPolynomial

noncomputable section

variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]

theorem isRelevant_iff (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsRelevant W ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsRelevant (R := R) W := Iff.rfl

section Homog

variable [DecidableEq K] [∀ k, Fintype (ι k)]

theorem weight_blockWeight (m : (Σ k, ι k) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight ι) m = fun k => ∑ i, m ⟨k, i⟩ := by
  funext k
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply]
  simp only [NumbersDVR.blockWeight, Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite,
    mul_one, mul_zero]
  classical
  set T : Finset (Σ k, ι k) := (Finset.univ : Finset (ι k)).map ⟨Sigma.mk k, sigma_mk_injective⟩
  have h1 : ∑ x ∈ m.support, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_left fun x _ hx => ?_
    rw [Finsupp.notMem_support_iff.mp hx, ite_self]
  have h2 : ∑ x ∈ T, (if k = x.1 then m x else 0) =
      ∑ x ∈ m.support ∪ T, (if k = x.1 then m x else 0) := by
    refine Finset.sum_subset Finset.subset_union_right fun x _ hx => ?_
    rw [if_neg]
    rintro rfl
    exact hx (Finset.mem_map.mpr ⟨x.2, Finset.mem_univ _, rfl⟩)
  rw [h1, ← h2, Finset.sum_map]
  simp

theorem isMultiHomog_iff (f : NumbersDVR.MRing ι R) (a : K → ℕ) :
    NumbersDVR.IsMultiHomog f a ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog (R := R) f a := by
  unfold NumbersDVR.IsMultiHomog ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog IsWeightedHomogeneous
  simp only [weight_blockWeight, mem_support_iff, funext_iff]

end Homog

section Ideals

variable [DecidableEq K] [∀ k, Fintype (ι k)]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiHomogIdeal P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := R) P := by
  classical
  constructor
  · intro h
    refine ⟨{g | ∃ f ∈ P, ∃ b, g = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f},
      ?_, le_antisymm ?_ ?_⟩
    · rintro g ⟨f, -, b, rfl⟩
      exact ⟨b, (isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)⟩
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact h f hf b
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hom : (Ideal.span S).IsHomogeneous
        (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
      refine Ideal.homogeneous_span _ S fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (isMultiHomog_iff x a).mpr ha⟩
    exact weightedHomogeneousComponent_mem_of_mem (h := hom) (hp := hf) (m := b)

theorem isMultiProjPrime_iff (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime (R := R) P :=
  ⟨fun h => ⟨h.isPrime, (isMultiHomogIdeal_iff P).mp h.multiHomog, h.relevant⟩,
    fun h => ⟨h.1, (isMultiHomogIdeal_iff P).mpr h.2.1, h.2.2⟩⟩

end Ideals

section Cycles

theorem multAt_eq_toNat (J W : Ideal (NumbersDVR.MRing ι R)) [W.IsPrime] :
    ReciprocityTheory.ChartRestriction.G.Geo.multAt (R := R) J W = (NumbersDVR.multAt J W).toNat := by
  unfold ReciprocityTheory.ChartRestriction.G.Geo.multAt NumbersDVR.multAt
  rw [dif_pos ‹W.IsPrime›]

theorem divCycle_eq [Fintype K] [∀ k, Fintype (ι k)] [IsNoetherianRing R]
    (P : Ideal (NumbersDVR.MRing ι R)) (f : NumbersDVR.MRing ι R) (W : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.divCycle P f W = (ReciprocityTheory.ChartRestriction.G.Geo.divCycle (R := R) P f W : ℤ) := by
  classical
  unfold NumbersDVR.divCycle ReciprocityTheory.ChartRestriction.G.Geo.divCycle
  simp only [Finsupp.ofSupportFinite_coe, ReciprocityTheory.ChartRestriction.G.Geo.divSupp, Set.mem_ofPred_eq,
    ← isRelevant_iff]
  split_ifs with h
  · have : W.IsPrime := h.1.1.1
    rw [multAt_eq_toNat]
  · rfl

end Cycles

end

end GroundTheory.Heights₂.Heights.Bridge
