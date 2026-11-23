import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenMeetingFibresPullbackSpecRingHom
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affineOpen_meeting_fibres_pullback_specRingHom : ∀ {R R' : Type} [CommRing R] [CommRing R'] (a : R →+* R') (A : Over (Sp R)) (W : A.left.Opens), IsAffineOpen W → (∀ t ∈ Set.range (spMap a), ∃ x ∈ W, A.hom x = t) → ∃ V : ((Over.pullback (spMap a)).obj A).left.Opens, IsAffineOpen V ∧ ∀ s : Sp R', ∃ x ∈ V, ((Over.pullback (spMap a)).obj A).hom x = s := by
  first | exact @GlobalTheory.affine_preimage_pullback_meets_fibres | exact GlobalTheory.affine_preimage_pullback_meets_fibres | (intros; apply GlobalTheory.affine_preimage_pullback_meets_fibres <;> assumption)
