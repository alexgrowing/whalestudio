import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvarianceRationalToRealSymplectic
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsTateZero
open CategoryTheory AlgebraicGeometry Set Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.ArInt GlobalTheory.TorsionForm GlobalTheory.ThetaRR
open GlobalTheory.LB (toMod)
open GlobalTheory.LieVB (omega)
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe (Fl Pt stdLat symMat tauU siegel symPart ChernIsFlat IsMetric InducesPolarisation cov)
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.invariance_rational_to_real_symplectic : ∀ (g : ℕ) (F : symMat g → symMat g → Ext (1 + 1)), IsHermFun g F → (∀ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, (∀ i l, ∃ r : ℚ, γ.mat i l = r) → IsInvFun F γ) → ∀ γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g, IsInvFun F γ := by
  first | exact @GlobalTheory.ThetaRR.isInvFun_of_rat | exact GlobalTheory.ThetaRR.isInvFun_of_rat | (intros; apply GlobalTheory.ThetaRR.isInvFun_of_rat <;> assumption)
