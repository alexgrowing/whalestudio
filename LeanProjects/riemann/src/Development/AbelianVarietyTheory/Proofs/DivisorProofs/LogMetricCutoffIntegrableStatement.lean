import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogMetricCutoffIntegrable
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
theorem _root_.GlobalTheory.T.log_metric_cutoff_integrable : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.HeightParts.KernelSt → GlobalTheory.HeightParts.OnCore fun _ O _ P =>
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t ≤ t₀ → ∀ (c : O.s.Comp) (σ : _ →+* ℂ)
      (ch : GlobalTheory.AlgChart (O.var c).str σ (O.var c).dim) (y : GlobalTheory.TrueGeo.Pts (O.var c) σ), y ∈ ch.e.source →
      Integrable (fun ξ => Real.log (O.met.r c σ (P.exph c σ ch y (t • ξ))) * GlobalTheory.ChernReg.cutoff (P.om c σ ch y ξ)) ∧
      rhoIn (P.om c σ) (P.exph c σ) (fun z => Real.log (O.met.r c σ z)) ch y t ≤ Real.log (C * Real.log (1 / t)) := by
  first | exact @GlobalTheory.LogMean.regLog_le_log_log | exact GlobalTheory.LogMean.regLog_le_log_log | (intros; apply GlobalTheory.LogMean.regLog_le_log_log <;> assumption)
