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

theorem openSubscheme_closedFibre_lift (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R')
    (X X' : Scheme.{0}) (f : X ⟶ Sp R) (f' : X' ⟶ Sp R') (π : X' ⟶ X) (U : X'.Opens)
    (hφ : Function.Surjective φ) (h : IsPullback π f' f (spMap φ)) :
    ∃ (W : X.Opens) (ρ : U.toScheme ⟶ W.toScheme), ρ ≫ W.ι = U.ι ≫ π ∧
      IsPullback ρ (U.ι ≫ f') (W.ι ≫ f) (spMap φ) := by
  have hsp : IsClosedImmersion (spMap φ) :=
    IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom φ) hφ
  have hπ : IsClosedImmersion π :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsClosedImmersion) h.flip hsp
  obtain ⟨t, ht, hts⟩ :=
    (IsClosedImmersion.isClosedEmbedding π).isInducing.isOpen_iff.mp U.isOpen
  let W : X.Opens := ⟨t, ht⟩
  have hW : π ⁻¹ᵁ W = U := Opens.ext hts
  subst hW
  refine ⟨W, π ∣_ W, morphismRestrict_ι π W, ?_⟩
  exact IsPullback.paste_vert (isPullback_morphismRestrict π W) h

end GlobalTheory
