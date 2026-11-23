import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.PoitouTateDuality.PtfsDefs
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp

noncomputable section

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal

namespace PositivityTheory.Lit1.PTN

theorem repCmp {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    [TopologicalSpace H] [IsTopologicalGroup H] (θ : G ≃ₜ* H) {R M : Type} [CommRing R]
    [AddCommGroup M] [Module R M] [TopologicalSpace M] [DiscreteTopology M]
    (rho : Representation R G M) (hc : ContAction rho) :
    ∃ (A : Rep.{0} (ULift.{0} ℤ) H) (_ : IsDiscreteRep A) (eM : M ≃+ A.V),
      ∀ g m, eM (rho g m) = A.ρ (θ g) (eM m) := by
  obtain ⟨A, hA, eM, h⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep G R M rho hc
  refine ⟨Rep.res (θ.symm : H ≃* G).toMonoidHom A,
    IsDiscreteRep.res θ.symm.continuous (φ := (θ.symm : H ≃* G).toMonoidHom) A, eM, ?_⟩
  intro g m
  rw [h]
  show A.ρ g (eM m) = A.ρ ((θ.symm : H ≃* G) (θ g)) (eM m)
  congr 2
  exact (θ.symm_apply_apply g).symm

end PositivityTheory.Lit1.PTN
