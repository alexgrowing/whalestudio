import Mathlib
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.SpanBaseChangeCoordinates
import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.AdelicProofs.GramMat
open NumberField TensorProduct GroundTheory.Heights₂.Heights GlobalTheory.CompanionTheory.Ar.Lines Matrix
open scoped ComplexOrder nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseChange_inner_self_eq_gramMat_form : ∀ (L : Type) [Field L] [NumberField L] (B : HermitianBundle.{0} L) (F : Submodule (𝓞 L) B.carrier) (i : ℕ) (f : Fin i → F) (c : F →ₗ[𝓞 L] (Fin i → L)), (∀ x, ∃ (D : 𝓞 L) (a : Fin i → 𝓞 L), D ≠ 0 ∧ D • x = ∑ j, a j • f j ∧ ∀ j, (D : L) * c x j = a j) → ∀ (K : Type) [Field K] [NumberField K] [Algebra L K] (x : Fin i → K), x ∈ Submodule.span (𝓞 K) ((fun (w : Fin i → L) j => algebraMap L K (w j)) '' (LinearMap.range c : Submodule (𝓞 L) (Fin i → L))) → ∃ X : (B.baseChange K).carrier, ∀ τ : K →+* ℂ, ((B.baseChange K).metric.form τ).inner ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) ((1 : ComplexAt τ) ⊗ₜ[𝓞 K] X) = star (fun j => τ (x j)) ⬝ᵥ (gramMat B (τ.comp (algebraMap L K)) (fun j => (f j : B.carrier)) *ᵥ fun j => τ (x j)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length | exact GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length | (intros; apply GlobalTheory.CompanionTheory.Ar.Lines.Lift.lift_length <;> assumption)
