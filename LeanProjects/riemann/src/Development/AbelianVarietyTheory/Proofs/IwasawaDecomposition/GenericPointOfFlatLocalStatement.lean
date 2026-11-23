import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericPointOfFlatLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generic_point_of_flat_local : ∀ (X U : Scheme.{0}) [IsLocallyNoetherian X] (j : U ⟶ X) [IsOpenImmersion j], Dense (Set.range j) →
    (∀ x : X, IsDomain (X.presheaf.stalk x)) → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (ξ : Sp R ⟶ X),
    (Scheme.stalkClosedPointTo ξ).hom.Flat → ∃ y : Sp (FractionRing R) ⟶ U, y ≫ j = jK R ≫ ξ := by
  first | exact @GlobalTheory.GenPt.generic_factors_dense | exact GlobalTheory.GenPt.generic_factors_dense | (intros; apply GlobalTheory.GenPt.generic_factors_dense <;> assumption)
