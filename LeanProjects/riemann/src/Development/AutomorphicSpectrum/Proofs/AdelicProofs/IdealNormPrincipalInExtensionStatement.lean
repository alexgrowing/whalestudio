import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.IdealNormPrincipalInExtension
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
open NumberField GroundTheory.Heights₂.Heights
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ideal_norm_principal_in_extension : ∀ (K : Type) [Field K] [NumberField K] (I : Ideal (𝓞 K)), I ≠ ⊥ → ∃ (K' : Type) (_ : Field K') (_ : NumberField K') (_ : Algebra K K') (y : 𝓞 K'), y ≠ 0 ∧ y ∈ I.map (algebraMap (𝓞 K) (𝓞 K')) ∧ |((Algebra.norm ℚ (y : K') : ℚ) : ℝ)| = (I.absNorm : ℝ) ^ Module.finrank K K' := by
  first | exact @GlobalTheory.CompanionTheory.Lines.exists_principal_extension | exact GlobalTheory.CompanionTheory.Lines.exists_principal_extension | (intros; apply GlobalTheory.CompanionTheory.Lines.exists_principal_extension <;> assumption)
