import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExpCoordBoundLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsExponentialChartAtPointStatement
open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor
open scoped Topology ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exp_coord_bound_local : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (n g : ℕ) (e : OpenPartialHomeomorph (CxPts (genStr s.T.Z) σ) (Fin n → ℂ)) (ex : ExpMaps s.T.Z σ g), IsExpChart e ex → ∀ y₀ ∈ e.source, ∃ U ∈ 𝓝 y₀, ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ U, ∀ (f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)) (W : Letter S.Dw → Fin g → ℂ), Dirs (Z := s.T.Z) ⟨y, f⟩ (fun w => (ex y w).left) W → ∀ (τ : D.host.E →+* ℂ) (v : Fin (S.Dw.mult τ) → ℂ), ‖∑ b, v b • W ⟨τ, b⟩‖ ^ 2 ≤ C * (star v ⬝ᵥ x.gram y f τ *ᵥ v).re ∧ (star v ⬝ᵥ x.gram y f τ *ᵥ v).re ≤ C * ‖∑ b, v b • W ⟨τ, b⟩‖ ^ 2 := by
  first | exact @GlobalTheory.ExpChartMetric.h0_le_exp_coord | exact GlobalTheory.ExpChartMetric.h0_le_exp_coord | (intros; apply GlobalTheory.ExpChartMetric.h0_le_exp_coord <;> assumption)
