import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.DifferentGeneratorDualIntegral
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.different_generator_dual_integral : ∀ (A K : Type) [CommRing A] [Field K] [Algebra A K] [CharZero K] (E : Type) [Field E] [NumberField E] (σ : E →+* K) (d : A), Function.Injective (algebraMap A K) → (∀ a : 𝓞 E, σ (a : E) ∈ (algebraMap A K).range) → Submodule.span A {algebraMap A K d} = Submodule.span A {y : K | ∃ x ∈ differentIdeal ℤ (𝓞 E), y = σ (x : E)} → algebraMap A K d ≠ 0 ∧ (∀ k, algebraMap A K d * σ (dualInt E k) ∈ (algebraMap A K).range) ∧ ∃ u : Module.Free.ChooseBasisIndex ℤ (𝓞 E) → A, ∑ k, algebraMap A K (u k) * (algebraMap A K d * σ (dualInt E k)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | exact GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt | (intros; apply GlobalTheory.CompanionTheory.Ar.HT.different_generator_dualInt <;> assumption)
