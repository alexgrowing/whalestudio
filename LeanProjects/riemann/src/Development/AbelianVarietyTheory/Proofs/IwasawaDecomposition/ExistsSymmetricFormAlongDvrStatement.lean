import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSymmetricFormAlongDvr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_form_along_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsIntegrallyClosed R →
    ∀ (Dg : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : R →+* W),
    Function.Injective f → ∀ ϖ : W, Irreducible ϖ →
    ∃ be : LinearMap.BilinForm ℤ Dg.toPre.X, (∀ y z, be y z = be z y) ∧ FormAt Dg.toPre f ϖ be := by
  first | exact @GlobalTheory.PreValForm.main | exact GlobalTheory.PreValForm.main | (intros; apply GlobalTheory.PreValForm.main <;> assumption)
