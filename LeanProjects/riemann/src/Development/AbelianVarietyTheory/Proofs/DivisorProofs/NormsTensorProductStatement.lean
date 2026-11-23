import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsTensorProduct
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeModelInducesRootMetric
import Development.AbelianVarietyTheory.Definitions.Divisors.ReferenceMetricMulDualEqOne
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.norms_tensor_product : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (L₁ L₂ : HermLB V.p) (f₁ : Y.X → Y.Fn) (a₁ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₁ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) (f₂ : Y.X → Y.Fn) (a₂ : ∀ σ : F →+* ℂ, Pts Y σ → ℝ) (l₂ : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ), Norms V L₁ f₁ a₁ l₁ → Norms V L₂ f₂ a₂ l₂ → Norms V (L₁.tens L₂) (fun x => f₁ x * f₂ x) (fun σ y => a₁ σ y + a₂ σ y) (fun v e y => l₁ v e y + l₂ v e y) := by
  first | exact @GlobalTheory.CoverNorm.norms_tens | exact GlobalTheory.CoverNorm.norms_tens | (intros; apply GlobalTheory.CoverNorm.norms_tens <;> assumption)
