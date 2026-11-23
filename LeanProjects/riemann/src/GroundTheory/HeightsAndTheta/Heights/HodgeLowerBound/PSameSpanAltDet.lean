import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

theorem SameSpanAltDet.proof : SameSpanAltDet.Statement := by
  intro Ω _ E _ _ r u u' hu hu' hspan
  let S := Submodule.span Ω (Set.range u')
  let B' : Module.Basis (Fin r) Ω S := Module.Basis.span hu'
  have hmem : ∀ a, u a ∈ S := fun a => by
    change u a ∈ Submodule.span Ω (Set.range u')
    rw [← hspan]
    exact Submodule.subset_span ⟨a, rfl⟩
  let v : Fin r → S := fun a => ⟨u a, hmem a⟩
  have hv : LinearIndependent Ω v := LinearIndependent.of_comp S.subtype hu
  have : FiniteDimensional Ω S := Module.Finite.of_basis B'
  have hcard : Fintype.card (Fin r) = Module.finrank Ω S := (Module.finrank_eq_card_basis B').symm
  let B : Module.Basis (Fin r) Ω S := basisOfLinearIndependentOfCardEqFinrank' v hv hcard
  have hB : ⇑B = v := coe_basisOfLinearIndependentOfCardEqFinrank' v hv hcard
  refine ⟨B'.det v, ?_, ?_⟩
  · rw [← hB]
    exact (B'.isUnit_det B).ne_zero
  · intro φ
    have key := congrArg (fun f => f v) (AlternatingMap.eq_smul_basis_det B' (φ.compLinearMap S.subtype))
    have hB' : (fun i => S.subtype (B' i)) = u' := funext fun a => Module.Basis.coe_span_apply hu' a
    have hv' : (fun i => S.subtype (v i)) = u := rfl
    simp only [AlternatingMap.compLinearMap_apply, AlternatingMap.smul_apply, smul_eq_mul] at key
    rw [hB', hv'] at key
    rw [key, mul_comm]

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
