import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsCountableHolomorphicFamiliesSmooth
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.ExistsHolomorphicFamily
import Development.AbelianVarietyTheory.Proofs.HeightProofs.DenseMvPolynomialEvalNeZero
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsEmbeddingsOverInjective
open Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_countable_holomorphic_families_smooth : ∀ (K A : Type) [Field K] [NumberField K] [CommRing A] [IsDomain A] [Algebra K A] [Algebra.Smooth K A] (σ : K →+* ℂ), ∃ (ι : Type) (_ : Countable ι) (m : ι → ℕ) (B : ∀ i, Set (Fin (m i) → ℂ)) (φ : ∀ i, (Fin (m i) → ℂ) → (A →+* ℂ)), (∀ i, IsOpen (B i)) ∧ (∀ i, ∀ b ∈ B i, (φ i b).comp (algebraMap K A) = σ) ∧ (∀ i (a : A), DifferentiableOn ℂ (fun b => φ i b a) (B i)) ∧ (∀ ψ : A →+* ℂ, ψ.comp (algebraMap K A) = σ → ∃ i, ∃ b ∈ B i, φ i b = ψ) ∧ ∀ i, ∀ b ∈ B i, ∀ a : A, a ≠ 0 → ∃ᶠ b' in 𝓝 b, φ i b' a ≠ 0 := by
  first | exact @GlobalTheory.SmoothPointCover.exists_countable_families | exact GlobalTheory.SmoothPointCover.exists_countable_families | (intros; apply GlobalTheory.SmoothPointCover.exists_countable_families <;> assumption)
