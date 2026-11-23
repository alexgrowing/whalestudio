import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelLemmaSmallVector
import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ArakelovDegreeEqDegreeOfFamily
open NumberField ReciprocityTheory.GeometryOfNumbersTheory
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.siegel_lemma_small_vector : ∀ (K : Type) [Field K] [NumberField K] (r : ℕ) (hE : HermFam K (Fin r → K)) (E : Submodule (𝓞 K) (Fin r → K)) (V : Submodule K (Fin r → K)) (f : (Fin r → K) →ₗ[K] K) (u : Fin r → K) (B : (K →+* ℂ) → ℝ), E.FG → Submodule.span K (E : Set (Fin r → K)) = ⊤ → u ∈ E → u ∈ V → f u ≠ 0 → (∀ σ, 0 < B σ) → (∀ (σ : K →+* ℂ) (q : ℕ) (v : Fin q → Fin r → K) (c : Fin q → ℂ), (∀ a, v a ∈ V) → ‖∑ a, c a * σ (f (v a))‖ ^ 2 ≤ B σ ^ 2 * (∑ a, ∑ b, starRingEnd ℂ (c a) * c b * hE.form σ (v a) (v b)).re) → deg hE (E ⊓ V.restrictScalars (𝓞 K)) - deg hE (E ⊓ (V ⊓ LinearMap.ker f).restrictScalars (𝓞 K)) ≤ (Real.log ((Submodule.span (𝓞 K) {f u}).toAddSubgroup.relIndex ((E ⊓ V.restrictScalars (𝓞 K)).map (f.restrictScalars (𝓞 K))).toAddSubgroup : ℝ) - ∑ σ : K →+* ℂ, Real.log ‖σ (f u)‖ + ∑ σ : K →+* ℂ, Real.log (B σ)) / Module.finrank ℚ K := by
  first | exact @GlobalTheory.SlopeStep.slope_step | exact GlobalTheory.SlopeStep.slope_step | (intros; apply GlobalTheory.SlopeStep.slope_step <;> assumption)
