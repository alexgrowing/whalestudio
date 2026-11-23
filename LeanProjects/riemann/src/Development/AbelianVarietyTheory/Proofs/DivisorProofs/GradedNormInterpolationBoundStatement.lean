import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GradedNormInterpolationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TendstoUniformlyOfFamAt
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsX
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open GlobalTheory.CovTestDR GlobalTheory.VdmRec GlobalTheory.MetFam GlobalTheory.ShFam GlobalTheory.Toroidal GlobalTheory.CxPts
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.graded_norm_interpolation_bound : ∀ (ι : Type) [Fintype ι] (m : ι → ℕ) (g : ℕ), g = ∑ τ, m τ → ∀ (Ψ : ι → Prop) (M₀ M : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) ℂ), (∀ τ, (M₀ τ).PosDef) → (∀ τ, (M τ).PosDef) → ∀ (v : Fin g → ∀ τ, Fin (m τ) → ℂ) (G : ℝ → Matrix (Fin g) (Fin g) ℂ), (∀ s a b, G s a b = ∑ τ, HermFrame.form (if Ψ τ then GradedNorm.mix s (M₀ τ) (M τ) else GradedNorm.mixDual s (M₀ τ) (M τ))⁻¹ (v a τ) (v b τ)) → IsUnit (G 1).det → ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ s₀ ∈ Set.Ico (0 : ℝ) 1, ∀ s₁ ∈ Set.Ico (0 : ℝ) 1, s₁ ≠ s₀ → ∀ (l l₁ : ℂ) (V : Matrix (Fin g) (Fin g) ℂ), l = ((1 - s) / (1 - s₀) : ℝ) → l₁ = ((1 - s₁) / (1 - s₀) : ℝ) → V = G s₀ * (G 1)⁻¹ - 1 → IsUnit (1 + (1 - l) • V).det → G s = (1 + l • V + (l * (1 - l) / (l₁ * (1 - l₁))) • ((G s₁ * (G 1)⁻¹ - 1 - l₁ • V) * (1 + (1 - l₁) • V) * (1 + (1 - l) • V)⁻¹)) * G 1 := by
  first | exact @GlobalTheory.DualGramInterp.gram_interp_formula | exact GlobalTheory.DualGramInterp.gram_interp_formula | (intros; apply GlobalTheory.DualGramInterp.gram_interp_formula <;> assumption)
