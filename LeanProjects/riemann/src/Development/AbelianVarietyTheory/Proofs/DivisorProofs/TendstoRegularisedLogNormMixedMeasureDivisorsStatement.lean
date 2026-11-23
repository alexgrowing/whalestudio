import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoRegularisedLogNormMixedMeasureDivisors
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DensConst
import Development.AbelianVarietyTheory.Definitions.Divisors.ContinuousBcPt
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAmbOfIsArithVar
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
import ReciprocityTheory.AnalyticForms.PotentialTheory.ProjectiveLineFubiniStudyFacts
open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.Points GlobalTheory.CechPic GlobalTheory.ChartGlue GlobalTheory.Mix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_regularisedLogNorm_mixedMeasure_divisors : GlobalTheory.Published.Principalisation → ∀ (F : Type) [Field F] (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp F) (σ : F →+* ℂ) (e : ℕ), IsProjOver p → topologicalKrullDim X = (e + 1 : ℕ) → ∀ (N : MLine p σ) (t : N.B.Sec), (genericPoint X ∈ nonzeroLocus t → ∀ L : Fin (e + 1) → MLine p σ, Tendsto (fun n : ℕ => Mix.int L fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) atTop (𝓝 (2 * Mix.int L (N.logSec t)))) ∧ ∀ (L : Fin e → MLine p σ) (Δ : CartierDiv X), (∀ z, Δ.mult z ≠ 0 → z ∈ nonzeroLocus t) → Tendsto (fun n : ℕ => ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (fun y => Real.log (N.φ.nsq (secVal p σ t) y + 1 / ((n : ℝ) + 1))) z) atTop (𝓝 (2 * ∑ᶠ z, (Δ.mult z : ℝ) * cycInt L (N.logSec t) z)) := by
  first | exact @GlobalTheory.Mix.tendsto_logReg | exact GlobalTheory.Mix.tendsto_logReg | (intros; apply GlobalTheory.Mix.tendsto_logReg <;> assumption)
