import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyDerivativeRelationSemilinearPullback
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyDerivativeRelation_semilinearPullback : ∀ (R R' : Type) [CommRing R] [CommRing R'] (X X' : Scheme.{0}) (s : X ⟶ Sp R) (s' : X' ⟶ Sp R') (σ : R →+* R') (φ : X' ⟶ X) (h : φ ≫ s = s' ≫ spMap σ) (x : HO1 s) (n : ℕ) (y : Fin n → HO1 s) (w : Fin n → GlobForm s), DRel (OAff s) x y w → DRel (OAff s') (pullHO1 h x) (fun k ↦ pullHO1 h (y k)) (fun k ↦ GlobalTheory.CechDR.pullForm h (w k)) := by
  first | exact @GlobalTheory.dRel_pull | exact GlobalTheory.dRel_pull | (intros; apply GlobalTheory.dRel_pull <;> assumption)
