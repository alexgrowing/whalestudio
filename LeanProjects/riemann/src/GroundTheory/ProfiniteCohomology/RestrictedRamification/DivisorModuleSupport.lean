import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.DivisorModule
import GroundTheory.ProfiniteCohomology.CupProducts.Cocycles
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory

noncomputable section

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  {I : Type} {H : I → Type} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
  (φ : ∀ i, H i →* G) (hφ : ∀ i, Continuous (φ i)) (A : Type) [AddCommGroup A]

theorem finite_divFunEval_ne_zero (n : ℕ) (x : cohomology (divFunRep φ A) n) :
    {i | (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n).hom x ≠ 0}.Finite := by
  obtain ⟨z, rfl⟩ := cohomologyπ_surjective (divFunRep φ A) n x
  set c := cochainOf (divFunRep φ A) (cocycleι (divFunRep φ A) n z) with hc
  have hfin : (Set.range c).Finite := (isLocallyConstant_cochainOf _).range_finite
  have hT : (⋃ f ∈ Set.range c, {i | ((f : divFun φ A) : I → G → A) i ≠ 0}).Finite :=
    hfin.biUnion fun f _ => (f : divFun φ A).2.1
  refine hT.subset fun i hi => ?_
  by_contra hiT
  apply hi
  have hz : cocyclesMapAlong (φ i) (hφ i) (divFunEval φ A i) n z = 0 := by
    apply cocycleι_injective
    apply cochainOf_injective
    rw [cochainOf_cocycleι_cocyclesMapAlong, map_zero]
    funext h
    rw [divFunEval_hom_apply]
    have hmem : ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i = 0 := by
      by_contra hne
      exact hiT (Set.mem_biUnion ⟨_, rfl⟩ hne)
    change ((c (⇑(φ i) ∘ h) : divFun φ A) : I → G → A) i 1 = 0
    rw [hmem]
    rfl
  change (cohomologyMapAlong (φ i) (hφ i) (divFunEval φ A i) n) (cohomologyπ (divFunRep φ A) n z) = 0
  rw [cohomologyMapAlong_cohomologyπ, hz, map_zero]

end

end GroundTheory.ProfCoh
