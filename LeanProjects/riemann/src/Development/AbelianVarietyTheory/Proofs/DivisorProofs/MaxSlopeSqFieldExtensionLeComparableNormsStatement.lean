import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaxSlopeSqFieldExtensionLeComparableNorms
import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
import Formalism.MeanHeightDescent.CovolumeFullAssemblyWeighted
open NumberField GlobalTheory.AllWt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.maxSlope_sq_fieldExtension_le_comparable_norms : ∀ (K K' V V' : Type) [Field K] [NumberField K] [IsTotallyComplex K] [Field K'] [NumberField K'] [Algebra K K'] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K' V'] [Module (𝓞 K') V'] [IsScalarTower (𝓞 K') K' V'] (N : (K →+* ℂ) → V → ℝ) (N' : (K' →+* ℂ) → V' → ℝ) (ι : V →ₛₗ[algebraMap K K'] V') (L : Submodule (𝓞 K) V) (c : (K' →+* ℂ) → ℝ) (B : ℝ), HasGram N → HasGram N' → (∀ σ x, N ((starRingEnd ℂ).comp σ) x = N σ x) → (∀ (n : ℕ) (b : Fin n → V), LinearIndependent K b → LinearIndependent K' (fun k => ι (b k))) → L.FG → L ≠ ⊥ → (∀ σ', 0 < c σ' ∧ |Real.log (c σ')| ≤ B) → (∀ σ' x, N' σ' (ι x) = c σ' * N (σ'.comp (algebraMap K K')) x) → slopeMax_sq N' (Submodule.span (𝓞 K') (ι '' (L : Set V))) ≤ slopeMax_sq N L + 2 * B := by
  first | exact @GlobalTheory.SlopeMaxExt.slopeMax_sq_span_le | exact GlobalTheory.SlopeMaxExt.slopeMax_sq_span_le | (intros; apply GlobalTheory.SlopeMaxExt.slopeMax_sq_span_le <;> assumption)
