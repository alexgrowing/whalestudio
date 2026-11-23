import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionSubordinateToFan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.starSubdivision_subordinate_to_fan : ∀ (O : Type) [CommRing O] (bar : O → O) (q : ℕ) (ψ w ψ' : InvFun O), IsStarOf bar q ψ w ψ' → Subordinate bar q ψ' ψ := by
  first | exact @GlobalTheory.PolFan.subordinate_of_isStarOf | exact GlobalTheory.PolFan.subordinate_of_isStarOf | (intros; apply GlobalTheory.PolFan.subordinate_of_isStarOf <;> assumption)
