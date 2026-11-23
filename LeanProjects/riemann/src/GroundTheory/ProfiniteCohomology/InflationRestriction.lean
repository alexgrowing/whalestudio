import Mathlib
import GroundTheory.ProfiniteCohomology.InflationRestriction.Higher
import GroundTheory.ProfiniteCohomology.InflationRestriction.FiveTerm
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory Limits

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (A : Rep.{u} k G) [IsDiscreteRep A]
  (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G))

theorem fiveTerm_exact :
    Function.Injective (cohomologyInfl A N 1).hom ∧
      LinearMap.range (cohomologyInfl A N 1).hom = LinearMap.ker (cohomologyResInv A N) ∧
      LinearMap.range (cohomologyResInv A N) = LinearMap.ker (transgression A N hN) ∧
      LinearMap.range (transgression A N hN) = LinearMap.ker (cohomologyInfl A N 2).hom := by
  refine ⟨cohomologyInfl_one_injective A N, ?_, ?_, ?_⟩
  · ext h
    constructor
    · rintro ⟨y, rfl⟩
      rw [LinearMap.mem_ker]
      apply Subtype.ext
      rw [coe_cohomologyResInv_apply, ZeroMemClass.coe_zero]
      have := congrArg (fun φ => ModuleCat.Hom.hom φ y) (cohomologyInfl_comp_cohomologyRes A N 0)
      simpa using this
    · intro hh
      exact exists_cohomologyInfl_one_eq A N h (congrArg Subtype.val hh)
  · ext h
    constructor
    · rintro ⟨g, rfl⟩
      exact transgression_cohomologyResInv A N hN g
    · intro hh
      exact exists_cohomologyResInv_eq A N hN h hh
  · ext t
    constructor
    · rintro ⟨h, rfl⟩
      exact cohomologyInfl_transgression A N hN h
    · intro ht
      exact exists_transgression_eq A N hN t ht

include hN in

theorem infRes_exact {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (cohomology (Rep.res N.subtype A) i)) :
    Function.Injective (cohomologyInfl A N q).hom ∧
      LinearMap.range (cohomologyInfl A N q).hom = LinearMap.ker (cohomologyRes A N q).hom :=
  ⟨cohomologyInfl_injective hN hq hA, range_cohomologyInfl_eq_ker_cohomologyRes hN hq hA⟩

end GroundTheory.ProfCoh
