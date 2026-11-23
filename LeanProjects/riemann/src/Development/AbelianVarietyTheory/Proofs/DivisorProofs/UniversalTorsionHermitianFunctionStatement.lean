import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalTorsionHermitianFunction
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
theorem _root_.GlobalTheory.T.universal_torsion_hermitian_function : GlobalTheory.Published.BismutKoehlerTorsion → Naturality → ∀ g : ℕ, ∃ F : symMat g → symMat g → Ext (1 + 1), IsHermFun g F ∧ ∀ s ∈ siegel g, ∀ (v : symMat g) (T : Ext (1 + 1)), IsUnivTorsion g s v T ↔ T = F s v := by
  first | exact @GlobalTheory.UnivTorsion.univTorsion_hermFun | exact GlobalTheory.UnivTorsion.univTorsion_hermFun | (intros; apply GlobalTheory.UnivTorsion.univTorsion_hermFun <;> assumption)
