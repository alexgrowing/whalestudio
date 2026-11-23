import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullClosedFormClass
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pull_closed_form_class : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (hc : Closed1 (OAff s) = ⊤) (hc' : Closed1 (OAff s') = ⊤) (w : GlobForm s), pullHH1 h (clAll (OAff s) hc w) = clAll (OAff s') hc' (GlobalTheory.CechDR.pullForm h w) := by
  first | exact @GlobalTheory.AbCoh.pullHH1_clAll | exact GlobalTheory.AbCoh.pullHH1_clAll | (intros; apply GlobalTheory.AbCoh.pullHH1_clAll <;> assumption)
