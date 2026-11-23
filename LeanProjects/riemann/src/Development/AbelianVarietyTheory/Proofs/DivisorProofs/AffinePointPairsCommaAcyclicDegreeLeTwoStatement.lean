import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffinePointPairsCommaAcyclicDegreeLeTwo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affinePointPairs_comma_acyclic_degree_le_two : (∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ∀ T : (IsSm κ t i).FullSubcategory, Desc.Sep ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧ Desc.Glue ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) ∧ Desc.Van1 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U)) ∧ ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0}) (t : X ⟶ Sp R) (Y : Scheme.{0}) (i : X ⟶ Y), (∀ U V : Y.Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V)) → ∀ T : (IsSm κ t i).FullSubcategory, Desc.Van2 ((IsSm κ t i).ι ⋙ Pr.fgt κ t i ⋙ O κ t) (fun S (_ : T ⟶ S) ↦ IsAffineOpen S.obj.U) := by
  first | exact @GlobalTheory.PDForm.isSm_acyclic_two | exact GlobalTheory.PDForm.isSm_acyclic_two | (intros; apply GlobalTheory.PDForm.isSm_acyclic_two <;> assumption)
