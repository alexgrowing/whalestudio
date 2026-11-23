import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JensenLogMeanCutoff
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
theorem _root_.GlobalTheory.T.jensen_log_mean_cutoff : ∀ {d : ℕ} (q g : (Fin d → ℂ) → ℝ), Continuous q → (∀ (t : ℝ) ξ, q (t • ξ) = t ^ 2 * q ξ) → (∀ ξ, ξ ≠ 0 → 0 < q ξ) → (∀ ξ, 1 ≤ g ξ) → MeasureTheory.Integrable (fun ξ => g ξ * GlobalTheory.ChernReg.cutoff (q ξ)) → MeasureTheory.Integrable (fun ξ => Real.log (g ξ) * GlobalTheory.ChernReg.cutoff (q ξ)) → GlobalTheory.ChernReg.mean q (fun ξ => Real.log (g ξ)) ≤ Real.log (GlobalTheory.ChernReg.mean q g) := by
  first | exact @GlobalTheory.jensen_log_mean | exact GlobalTheory.jensen_log_mean | (intros; apply GlobalTheory.jensen_log_mean <;> assumption)
