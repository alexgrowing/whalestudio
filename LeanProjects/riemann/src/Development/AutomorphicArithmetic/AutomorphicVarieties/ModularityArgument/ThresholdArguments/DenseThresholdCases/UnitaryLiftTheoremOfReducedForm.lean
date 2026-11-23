import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.UnitaryLiftTheoremOfReducedForm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ThmS6CoreS
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AfBridge

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Matrix IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.Aut UpperTheory.V.UnitaryThreeInertia
private theorem totDisc_quot {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (N : Subgroup G) [N.Normal] (hN : IsClosed (N : Set G)) :
    TotallyDisconnectedSpace (G ⧸ N) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  by_contra hx
  have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
  have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
  obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
  let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
  have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
  have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
  obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
  exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
theorem UpperTheory.V.UnitaryThreeInertia.unitary_lift_of_reduced_core :
    _root_.UpperTheory.V.Aut.ThmS6Core_s → _root_.UpperTheory.V.Aut.ThmS6_s := by
  intro h K _ _ _ hK Ω _ _ _ l _ ι c N _ e ψ o₁ hd S A F hF
  obtain ⟨g₁, hg, H⟩ := h K hK Ω l ι c N e ψ o₁ hd S A F hF
  refine ⟨g₁, hg, fun R _ _ _ u hu => ⟨(H R u hu).1, fun ξ r h1 h2 => ?_⟩⟩
  haveI : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  haveI hcl := isClosed_NS Ω (S : Set Pl)
  haveI : CompactSpace (Gam Ω S) := inferInstance
  haveI : T2Space (Gam Ω S) := inferInstance
  haveI : TotallyDisconnectedSpace (Gam Ω S) := totDisc_quot _ hcl
  have hOk := hostFrame_ok Ω c e ψ o₁ hd S A F hF
  have hz : F.IsCharZeroPt g₁ r := isCharZeroPt_of_isPtHom (l := l) F hOk g₁ hg u hu (H R u hu).1 ξ r h1
  exact ⟨matIrr_open Ω c e ψ o₁ hd S A F hF g₁ hg r hz h2, matIrr_cyc Ω c e ψ o₁ hd S A F hF g₁ hg r hz h2,
    (H R u hu).2 ξ r h1 h2⟩
end
