import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen

open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat
open Topology

namespace GlobalTheory.CompanionTheory.Ar.Flat.ValLift

theorem valAt_of_stalkMap_surjective : ∀ (X₀ X' : Scheme.{0}) (Ω R : Type) [Field Ω] [CommRing R] [IsLocalRing R]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X₀) (ξ' : Spec (CommRingCat.of Ω) ⟶ X') (π : X' ⟶ X₀)
    (z : Spec (CommRingCat.of R) ⟶ X') (a : Ω) (r : R), ξ' ≫ π = ξ →
    Function.Surjective (π.stalkMap (centre z)).hom → ValAt ξ' z a r → ValAt ξ (z ≫ π) a r := by
  intro X₀ X' Ω R _ _ _ ξ ξ' π z a r hξ hsurj hv
  subst hξ
  obtain ⟨h', s', hs'a, hs'r⟩ := hv
  obtain ⟨s, hs⟩ := hsurj s'
  have hsp : genPt (ξ' ≫ π) ⤳ centre (z ≫ π) := h'.map π.continuous
  refine ⟨hsp, s, ?_, ?_⟩
  · rw [← hs'a, ← hs]
    have key : X₀.presheaf.stalkSpecializes hsp ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π) =
        π.stalkMap (centre z) ≫ X'.presheaf.stalkSpecializes h' ≫ AlgebraicGeometry.Scheme.stalkClosedPointTo ξ' := by
      rw [AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
      exact AlgebraicGeometry.Scheme.Hom.stalkSpecializes_stalkMap_assoc π (genPt ξ') (centre z) h'
        (AlgebraicGeometry.Scheme.stalkClosedPointTo ξ')
    show (CommRingCat.Hom.hom (X₀.presheaf.stalkSpecializes hsp ≫
      AlgebraicGeometry.Scheme.stalkClosedPointTo (ξ' ≫ π))) s = _
    rw [key]
    rfl
  · rw [← hs'r, ← hs, AlgebraicGeometry.Scheme.stalkClosedPointTo_comp]
    rfl

end GlobalTheory.CompanionTheory.Ar.Flat.ValLift
