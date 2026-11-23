import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Definitions.Divisors.IsEtCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SameDiv
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.LogPair
open scoped TensorProduct

namespace GlobalTheory

theorem cls_canonLB_baseChange : ∀ (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (d : ℕ) [SmoothOfRelativeDimension d f] [SmoothOfRelativeDimension d f'] (K : CanonLB f d) (K' : CanonLB f' d), IsPullback π f' f (spMap φ) → cls K'.bundle K'.isLB = CechPic.pull π (cls K.bundle K.isLB) := by
  intro R R' _ _ φ X X' f f' π d _ _ K K' H
  rw [← cls_pull K.isLB π (K.baseChange H).isLB]
  exact (cls_eq_iff _ _).2 (CanonLB.lbIso K' (K.baseChange H))

end GlobalTheory
