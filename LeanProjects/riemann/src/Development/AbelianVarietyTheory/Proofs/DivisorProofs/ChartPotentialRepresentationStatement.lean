import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartPotentialRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogBallBd
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry MeasureTheory GlobalTheory.ChernReg GlobalTheory.ShFam GlobalTheory.CxPts Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_potential_representation : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → ∀ (D : D7) (O : Setup D) (x : GlobalTheory.ShFam.ToroidalCompactificationData O.s) (P : PolOf x O.Φ), O.CoreWith x P → 2 < D.R.f * (O.N - 1) → (∃ (A : SlopeTestRemainingChoices O.Y) (T : Real0 O.Y) (H : Ht O.Y), Nonempty (O.Reads A T H)) → ∀ (c : O.s.Comp) (σ : D.what₂.LL →+* ℂ) (y₀ : GlobalTheory.TrueGeo.Pts (O.var c) σ), ∃ (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (U : Set (ReciprocityTheory.L2DbarEstimates.V (O.var c).dim)) (Φ : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → (Fin (O.var c).dim → ℂ)) (H : ReciprocityTheory.L2DbarEstimates.V (O.var c).dim → ℝ) (I : Finset (Fin (O.var c).dim)), y₀ ∈ ch.e.source ∧ IsOpen U ∧ ch.e y₀ ∈ U ∧ U ⊆ ch.e.target ∧ ContDiffOn ℝ 1 Φ U ∧ Function.Bijective (fderiv ℝ Φ (ch.e y₀)) ∧ ContinuousOn H U ∧ ∀ v ∈ U, (∀ i ∈ I, Φ v i ≠ 0) → O.met.r c σ (ch.e.symm v) = H v - ∑ i ∈ I, Real.log (‖Φ v i‖ ^ 2) := by
  first | exact @GlobalTheory.CovTop.r_eq_sub_log_chart | exact GlobalTheory.CovTop.r_eq_sub_log_chart | (intros; apply GlobalTheory.CovTop.r_eq_sub_log_chart <;> assumption)
