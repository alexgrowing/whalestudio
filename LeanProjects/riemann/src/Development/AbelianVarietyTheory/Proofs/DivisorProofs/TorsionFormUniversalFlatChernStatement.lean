import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFormUniversalFlatChern
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
theorem _root_.GlobalTheory.T.torsion_form_universal_flat_chern : Naturality → ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] (g : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (j : Fl g → Pt E g → ℂ) (m : Pt E g → ℝ), Convex ℝ B → IsDatum B τ (stdLat g) j m → ChernIsFlat B τ m → ∀ b ∈ B, ∀ (e : E) (T : Ext (1 + 1)), IsTorsionForm τ (stdLat g) j m ![e] b T → IsUnivTorsion g (symPart (τ b)) (fderiv ℂ (fun x => symPart (τ x)) b e) T := by
  first | exact @GlobalTheory.UnivPullback.torsion_eq_univ | exact GlobalTheory.UnivPullback.torsion_eq_univ | (intros; apply GlobalTheory.UnivPullback.torsion_eq_univ <;> assumption)
