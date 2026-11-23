import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.IsUnitOrIsUnitOfAddOne
import Mathlib.Topology.Algebra.ClopenNhdofOne

open IsLocalRing Polynomial Matrix UpperTheory.V

theorem UpperTheory.V.Ws.exists_mem_open_inter_subgroup_of_cosetwise_finiteIndex :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
      (Z : Subgroup G) (P : G → Prop), (∀ V : Subgroup Z, V.FiniteIndex → ∀ σ : Z, ∃ g ∈ V, P (σ * g : Z)) →
      ∀ U : Set G, IsOpen U → (U ∩ (Z : Set G)).Nonempty → ∃ σ ∈ U ∩ (Z : Set G), P σ := by
  intro G _ _ _ _ _ Z P h U hU hne
  obtain ⟨σ, hσU, hσZ⟩ := hne
  have hW : IsOpen ((fun x : G => σ * x) ⁻¹' U) := hU.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ ((fun x : G => σ * x) ⁻¹' U) := by simpa using hσU
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  have hfi : (N.toSubgroup).FiniteIndex := by
    have := Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
    exact Subgroup.finiteIndex_of_finite_quotient
  obtain ⟨g, hg, hP⟩ := h (N.toSubgroup.subgroupOf Z) inferInstance ⟨σ, hσZ⟩
  refine ⟨_, ⟨?_, ((⟨σ, hσZ⟩ : Z) * g).2⟩, hP⟩
  exact hN (show (g : G) ∈ N.toSubgroup from hg)
