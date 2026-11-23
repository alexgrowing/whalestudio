import Mathlib
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal

noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.Mass.MeanV

variable {F : Type} [Field F] [NumberField F]

def IntOut (T : Finset (HeightOneSpectrum (𝓞 F))) : Set F :=
  {x | ∀ v, v ∉ T → algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F}

def GoodFac (v : HeightOneSpectrum (𝓞 F)) (lam : Measure (Fv F v)) (C : ℝ) (g : Fv F v → ℝ) : Prop :=
  ContinuousOn g {0}ᶜ ∧ (∀ s, s ∉ v.adicCompletionIntegers F → g s = 0) ∧
    (∀ s ∈ v.adicCompletionIntegers F, s ≠ 0 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ)) ∧
    (∀ s : Fv F v, Valued.v s = 1 → |g s - 1| ≤ C / (Ideal.absNorm v.asIdeal : ℝ) ^ 2) ∧ ∫ s, g s ∂lam = 1

def truncSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (T : Finset (HeightOneSpectrum (𝓞 F)))
    (ψ : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0}, (IntOut T).indicator
    (fun x => G (θ δ * algebraMap F (Ainf F) x) * ∏ v ∈ T, ψ v (algebraMap F (Fv F v) x)) β.1

def fullSum (θ : ℝ →+* Ainf F) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (δ : ℝ) : ℝ :=
  δ ^ Module.finrank ℚ F * ∑' β : {β : F // β ≠ 0},
    G (θ δ * algebraMap F (Ainf F) β.1) * ∏' v, g v (algebraMap F (Fv F v) β.1)

end GlobalTheory.CompanionTheory.Mass.MeanV

end
