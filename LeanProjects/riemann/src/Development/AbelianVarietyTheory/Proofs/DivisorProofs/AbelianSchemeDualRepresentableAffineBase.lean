import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDescendsToFinitelyGeneratedSubring
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeFiniteTypeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasProperSmoothDualRepresentativeGrpPullbackIffStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualCon

theorem hasRep_affine : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A →
    SmoothOfRelativeDimension g A.hom → HasRep A g (𝟙_ _) := by
  intro R _ A _ g hA hg
  obtain ⟨S, B, _, φ, -, hS, hB, hgB, hφ⟩ :=
    GlobalTheory.AbelianLimit.abelianScheme_descends_to_fg_subring R g A ∅ hA hg
  have h₀ : HasRep B g (𝟙_ _) := GlobalTheory.T.hasProperSmoothDualRepresentative_finiteType S B g hB hgB
  exact (GlobalTheory.T.hasProperSmoothDualRepresentative_grpPullback_iff _ _ _ B A φ hφ g (𝟙_ _)).1.2 (GlobalTheory.T.baseChangeBis _ B _ _ g (toUnit _) h₀)

end GlobalTheory.DualCon
