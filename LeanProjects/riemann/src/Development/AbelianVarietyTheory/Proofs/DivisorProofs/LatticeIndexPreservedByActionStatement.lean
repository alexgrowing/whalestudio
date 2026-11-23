import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIndexPreservedByAction
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFormCongrOfEventuallyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelActionPreservesFlatForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapSymplecticTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodMapRigidity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricTranslationPullbackFlat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatCoordsSymplecticPullbackForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DdcCompHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteQuotientOfIsLatLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelPeriodMapSimplyConnectedStatement
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_index_preserved_by_action : ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g), (∀ i l, ∃ r : ℚ, γ.mat i l = r) → ∃ M : Submodule ℤ (Fl g), IsLat M ∧ M ≤ stdLat g ∧ IsLat (latAct M γ) ∧ latAct M γ ≤ stdLat g ∧ 0 < Nat.card (stdLat g ⧸ M.submoduleOf (stdLat g)) ∧ Nat.card (stdLat g ⧸ M.submoduleOf (stdLat g)) = Nat.card (stdLat g ⧸ (latAct M γ).submoduleOf (stdLat g)) := by
  first | exact @GlobalTheory.ratSp_exists_sublat_same_index | exact GlobalTheory.ratSp_exists_sublat_same_index | (intros; apply GlobalTheory.ratSp_exists_sublat_same_index <;> assumption)
