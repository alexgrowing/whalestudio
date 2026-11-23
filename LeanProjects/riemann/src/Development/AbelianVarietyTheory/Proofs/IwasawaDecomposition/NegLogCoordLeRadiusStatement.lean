import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NegLogCoordLeRadius
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_log_coord_le_radius : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n a : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)), IsHolTo e.target (fun z => (e.symm z).1) → (∀ y ∈ e.source, Inner y ↔ ∀ k : Fin n, (k : ℕ) < a → e y k ≠ 0) → ∀ y₀ ∈ e.source, ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, Inner y → ∀ k : Fin n, (k : ℕ) < a → -Real.log ‖e y k‖ ≤ C * x.r σ y := by
  first | exact @GlobalTheory.ShFam.negLog_coord_le_mul_r | exact GlobalTheory.ShFam.negLog_coord_le_mul_r | (intros; apply GlobalTheory.ShFam.negLog_coord_le_mul_r <;> assumption)
