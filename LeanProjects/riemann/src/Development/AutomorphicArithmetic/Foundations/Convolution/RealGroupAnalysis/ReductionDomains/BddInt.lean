import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.ContinuousEntry
import GroundTheory.GlobalFields.TateThesis.AdeleScaling
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.WeilRepresentation.ImportsRest
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.ReductionDomains.VolD

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GJMatrix
open scoped Classical ENNReal NNReal Pointwise
open UpperTheory.ConvolutionTheory.R2

theorem UpperTheory.ConvolutionTheory.R2.M.bddInt :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (M₀ : Meas F), ∃ c : ℝ, 0 < c ∧ ∀ (u : G1 F → ℂ) (B : ℝ), (∀ γ g, ‖u (ratS F γ * g)‖ = ‖u g‖) → (∀ (b : A F) (a : (A F)ˣ), ∀ k ∈ KK F, c ≤ ab a → ‖u (nU b * mD a * k)‖ ≤ B) → (∀ g, ‖u g‖ ≤ B) ∧ (AEStronglyMeasurable u (M₀.μ.restrict M₀.D) → IntegrableOn u M₀.D M₀.μ) := by
  intro F _ _ _ M₀
  obtain ⟨c, hc, hred⟩ := UpperTheory.ConvolutionTheory.R2.red F
  refine ⟨c, hc, fun u B hinv hB => ?_⟩
  have hall : ∀ g, ‖u g‖ ≤ B := by
    intro g
    obtain ⟨γ, b, a, k, hk, hg, hca⟩ := hred g
    rw [← hinv γ g, hg]
    exact hB b a k hk hca
  refine ⟨hall, fun hm => ?_⟩
  haveI : IsFiniteMeasure (M₀.μ.restrict M₀.D) :=
    ⟨by simpa using UpperTheory.ConvolutionTheory.R2.M.volD F M₀⟩
  exact Integrable.of_bound hm B (Eventually.of_forall hall)
