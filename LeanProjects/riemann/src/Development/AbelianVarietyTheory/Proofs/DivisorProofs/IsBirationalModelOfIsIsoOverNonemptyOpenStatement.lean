import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBirationalModelOfIsIsoOverNonemptyOpen
import Development.AbelianVarietyTheory.Definitions.Divisors.SmallFam
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SmallSecTensTriv
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSNef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBirationalModel_of_isIso_over_nonempty_open : ∀ (X Y : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (π : Y ⟶ X) (U : X.Opens), (U : Set X).Nonempty → IsIso (π ∣_ U) → ∃ φ : X.functionField →+* Y.functionField, IsModel π φ := by
  first | exact @GlobalTheory.HSNef.isModel_of_isIso_restrict | exact GlobalTheory.HSNef.isModel_of_isIso_restrict | (intros; apply GlobalTheory.HSNef.isModel_of_isIso_restrict <;> assumption)
