import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaneChainDescentFirst
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
theorem _root_.GlobalTheory.T.universal_torsion_rational_symplectic_invariance : GlobalTheory.Published.BismutKoehlerTorsion → Naturality → ∀ (g : ℕ) (γ : GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe.Sp g), (∀ i l, ∃ r : ℚ, γ.mat i l = r) → ∀ s ∈ siegel g, actB γ s ∈ siegel g ∧ ∀ (v : symMat g) (T : Ext (1 + 1)), IsUnivTorsion g (actB γ s) (fderiv ℂ (actB γ) s v) T → IsUnivTorsion g s v T := by
  first | exact @GlobalTheory.RatInv.univTorsion_ratInv | exact GlobalTheory.RatInv.univTorsion_ratInv | (intros; apply GlobalTheory.RatInv.univTorsion_ratInv <;> assumption)
