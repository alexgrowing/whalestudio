import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormDbarFormSubLogMetricLe
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqOfNonneg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.CurveDens GlobalTheory.Cartier
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norm_dbar_form_sub_log_metric_le : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] (G : E → Matrix (Fin 1 ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℂ) (s : E → Fin 1 ⊕ Fin 1 → ℂ) (ξ z : E), MContDiffAt 1 G z → (∀ᶠ x in 𝓝 z, (G x).PosDef) → (∀ i, DifferentiableAt ℂ (fun x => s x i) z) → ‖dbar (fun x => form (G x) (s x) (Pi.single (Sum.inl 0) 1)) z ξ - form (G z) (s z) (Pi.single (Sum.inl 0) 1) * dbar (fun x => (Real.log (G x (Sum.inl 0) (Sum.inl 0)).re : ℂ)) z ξ‖ ^ 2 = ((G z (Sum.inl 0) (Sum.inl 0)).re * (form (G z) (s z) (s z)).re - ‖form (G z) (s z) (Pi.single (Sum.inl 0) 1)‖ ^ 2) * (Real.pi * (2 * diagVal (extTrace G z) ξ)) := by
  first | exact @GlobalTheory.CurveDens.norm_sq_dbar_proj_rank_two | exact GlobalTheory.CurveDens.norm_sq_dbar_proj_rank_two | (intros; apply GlobalTheory.CurveDens.norm_sq_dbar_proj_rank_two <;> assumption)
