import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChernDensityFrameIndepChartJacobianFactor
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopChernDensityInvariantHolomorphicFrameChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernTopChartIndependent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHolomorphicInvertibleFrameCoordinates
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open Filter Topology
open scoped Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chern_density_frame_indep_chart_jacobian_factor : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {ι : Type} [Finite ι] {m : ι → ℕ} (E : Fr (ratOf X) m 0) (O : X.X.Opens) (H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ), IsMetricOn E O H → ∀ (R : MvPolynomial (ι × ℕ) ℝ) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → ∀ (c c' : AlgChart X.str σ X.dim), y ∈ c.e.source → y ∈ c'.e.source → ∀ {A A' : Mat m X.Fn}, A ∈ E.S (under y) → A' ∈ E.S (under y) → chernTop R (fun v => H A (c.e.symm v)) (c.e y) = ‖transDet c.e c'.e y‖ ^ 2 * chernTop R (fun v => H A' (c'.e.symm v)) (c'.e y) := by
  first | exact @GlobalTheory.GoodMetric.chernTop_frame_chart_trans | exact GlobalTheory.GoodMetric.chernTop_frame_chart_trans | (intros; apply GlobalTheory.GoodMetric.chernTop_frame_chart_trans <;> assumption)
