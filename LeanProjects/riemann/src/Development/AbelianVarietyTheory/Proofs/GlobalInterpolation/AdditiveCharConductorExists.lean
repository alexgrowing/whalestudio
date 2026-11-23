import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ImportsTer
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOneOfNormSubOneLt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsConductorAdicCompletion

open scoped TensorProduct
open NumberField IsDedekindDomain

namespace GlobalTheory.CharConductor

theorem eq_one_of_pow_near_one {z : ℂ} (h : ∀ n : ℕ, ‖z ^ n - 1‖ < 1 / 2) : z = 1 := by
  first
  | exact @_root_.GlobalTheory.IterationConvergence.main
  | exact _root_.GlobalTheory.IterationConvergence.main
  | (apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IterationConvergence.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IterationConvergence.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IterationConvergence.main ..)

theorem exists_exponent_of_valued {K : Type} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    (ψ : AddChar K ℂ) (hψ : Continuous ψ) (hne : ∃ t, ψ t ≠ 1) :
    ∃ n : ℤ, ∀ t : K, (∀ s : K, Valued.v s ≤ (1 : WithZero (Multiplicative ℤ)) → ψ (t * s) = 1) ↔
      Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor
  | (apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)
  | (intros; apply _root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CharacterConductorBall.exists_conductor <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CharacterConductorBall.exists_conductor ..)

theorem exists_conductor_exponent : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (ψ : AddChar (v.adicCompletion F) ℂ), Continuous ψ → (∀ t, ‖ψ t‖ = 1) → (∃ t, ψ t ≠ 1) → ∃ n : ℤ, ∀ t : v.adicCompletion F, (∀ s ∈ v.adicCompletionIntegers F, ψ (t * s) = 1) ↔ Valued.v t ≤ WithZero.exp n := by
  first
  | exact @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
  | exact _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion
  | (apply _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConductorAdicCompletion.exists_conductor_adicCompletion ..)

end GlobalTheory.CharConductor
