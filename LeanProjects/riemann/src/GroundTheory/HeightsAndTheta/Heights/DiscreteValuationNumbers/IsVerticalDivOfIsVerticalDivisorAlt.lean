import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Objects
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.MemOfMemSupportDivCycle
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

open MvPolynomial

noncomputable section

namespace Objects

variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]

section Ring

variable {R : Type*} [CommRing R]

theorem weight_blockWeight_apply (m : (Σ k, ι k) →₀ ℕ) (k : K) :
    Finsupp.weight (blockWeight ι) m k = ∑ i, m ⟨k, i⟩ := by
  classical
  rw [Finsupp.weight_apply,
    Finsupp.sum_fintype m (fun i c => c • blockWeight ι i) (fun i => zero_smul ℕ _),
    Finset.sum_apply, Fintype.sum_sigma]
  simp [blockWeight, Pi.single_apply]

theorem isMultiHomog_iff (f : MRing ι R) (b : K → ℕ) :
    IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b := by
  constructor
  · intro h m hm k
    rw [← weight_blockWeight_apply, h (mem_support_iff.mp hm)]
  · intro h m hm
    funext k
    rw [weight_blockWeight_apply, h m (mem_support_iff.mpr hm) k]

attribute [local instance] MvPolynomial.weightedGradedAlgebra

theorem isMultiHomogIdeal_iff (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal I := by
  classical
  constructor
  · intro h
    refine ⟨{x | x ∈ I ∧ ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog x a}, fun f hf => hf.2, ?_⟩
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr fun x hx => hx.1)
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨h f hf b, b, ?_⟩
    exact (isMultiHomog_iff _ b).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hI : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
      refine Ideal.homogeneous_span _ _ fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((isMultiHomog_iff x a).mpr ha)⟩
    exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hI hf b

theorem isMultiProjPrime_iff (P : Ideal (MRing ι R)) :
    IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P :=
  ⟨fun h => ⟨h.isPrime, (isMultiHomogIdeal_iff P).mp h.multiHomog, h.relevant⟩,
    fun h => ⟨h.1, (isMultiHomogIdeal_iff P).mpr h.2.1, h.2.2⟩⟩

omit [DecidableEq K] in

theorem intCyc_divCycle [IsNoetherianRing R] (P : Ideal (MRing ι R)) (s : MRing ι R)
    (W : Ideal (MRing ι R)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W =
      divCycle P s W := by
  classical
  have hc : (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s : Ideal (MRing ι R) → ℕ) W =
      if W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s then
        ReciprocityTheory.ChartRestriction.G.Geo.multAt (P ⊔ Ideal.span {s}) W else 0 := by
    unfold ReciprocityTheory.ChartRestriction.G.Geo.divCycle
    rw [Finsupp.ofSupportFinite_coe]
  rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc, Finsupp.mapRange_apply, hc, divCycle]
  by_cases h : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes ∧ IsRelevant W
  · have h' : W ∈ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := h
    rw [if_pos h', dif_pos h, ReciprocityTheory.ChartRestriction.G.Geo.multAt, dif_pos h.1.1.1]
    all_goals rfl
  · have h' : W ∉ ReciprocityTheory.ChartRestriction.G.Geo.divSupp P s := h
    rw [if_neg h', dif_neg h, Nat.cast_zero]

end Ring

section DVR

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem divO_eq_ratDiv (P : Ideal (MRing ι O)) (f g : MRing ι O) (W : Ideal (MRing ι O)) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO P f g W = ratDiv P f g W := by
  rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO, Finsupp.sub_apply, intCyc_divCycle,
    intCyc_divCycle, ratDiv]

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

theorem redEval_eq_cycEval (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ)
    (Z : Ideal (MRing ι O) →₀ ℤ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval J Z =
      cycEval (fun W => J (specialIdeal W)) Z := by
  classical
  rw [GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval, cycEval,
    finsum_eq_sum_of_support_subset _ (s := Z.support) fun W hW =>
      Finsupp.mem_support_iff.mpr (left_ne_zero_of_mul (Function.mem_support.mp hW))]
  rfl

omit [IsDomain O] [IsDiscreteValuationRing O] in

theorem isModelOver_iff (P : Ideal (MRing ι O)) (d : ℕ) :
    IsModelOver P d ↔ GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.IsModelOver P d :=
  ⟨fun h => ⟨(isMultiProjPrime_iff P).mp h.multiProj, h.noTorsion, h.dim⟩,
    fun h => ⟨(isMultiProjPrime_iff P).mpr h.1, h.2.1, h.2.2⟩⟩

end DVR

theorem equiv (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    (∀ (f : MRing ι O) (b : K → ℕ), IsMultiHomog f b ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog f b) ∧
    (∀ P : Ideal (MRing ι O), IsMultiProjPrime P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiProjPrime P) ∧
    (∀ (P : Ideal (MRing ι O)) (s : MRing ι O) (W : Ideal (MRing ι O)),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.intCyc (ReciprocityTheory.ChartRestriction.G.Geo.divCycle P s) W =
        divCycle P s W) ∧
    (∀ (P : Ideal (MRing ι O)) (f g : MRing ι O) (W : Ideal (MRing ι O)),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.divO P f g W = ratDiv P f g W) ∧
    (∀ (J : Ideal (MRing ι (IsLocalRing.ResidueField O)) → ℤ) (Z : Ideal (MRing ι O) →₀ ℤ),
      GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.redEval J Z =
        cycEval (fun W => J (specialIdeal W)) Z) :=
  ⟨isMultiHomog_iff, isMultiProjPrime_iff, intCyc_divCycle, divO_eq_ratDiv, redEval_eq_cycEval⟩

end Objects

end

end GroundTheory.Heights₂.Heights.NumbersDVR
