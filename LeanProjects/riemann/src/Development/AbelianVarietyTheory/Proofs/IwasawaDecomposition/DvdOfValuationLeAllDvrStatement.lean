import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdOfValuationLeAllDvr
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvd_of_valuation_le_all_dvr : ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R], IsNoetherianRing R → IsIntegrallyClosed R →
    ∀ r s : R, r ≠ 0 →
    (∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ ϖ : W, Irreducible ϖ → ∀ f : R →+* W,
      Function.Injective f → ∀ n m : ℕ, Associated (f r) (ϖ ^ n) → Associated (f s) (ϖ ^ m) → n ≤ m) → r ∣ s := by
  first | exact @GlobalTheory.dvd_of_forall_complete_dvr_order_le | exact GlobalTheory.dvd_of_forall_complete_dvr_order_le | (intros; apply GlobalTheory.dvd_of_forall_complete_dvr_order_le <;> assumption)
