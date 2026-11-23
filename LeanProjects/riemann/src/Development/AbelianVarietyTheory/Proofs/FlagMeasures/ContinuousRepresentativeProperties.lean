import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtAeEqContRep

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff

namespace GlobalTheory.ContRepUniq

theorem lintegral_enorm_sq_eq {X : Type} [MeasurableSpace X] (μ : Measure X) (F : Lp ℂ 2 μ) :
    ∫⁻ x, ‖F x‖ₑ ^ 2 ∂μ = ENNReal.ofReal (‖F‖ ^ 2) := by
  rw [Lp.norm_def, ENNReal.ofReal_pow ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top F),
    eLpNorm_eq_lintegral_rpow_enorm two_ne_zero ENNReal.ofNat_ne_top]
  have h2 : ((2 : ENNReal).toReal) = 2 := by norm_num
  simp only [h2, ← ENNReal.rpow_two]
  rw [← ENNReal.rpow_mul]
  norm_num

theorem contRep_unique_linear : ∀ (B : RowsAut), (∀ F f f', IsContRep B F f → IsContRep B F f' → f = f') ∧ (∀ F F' f f' (c : ℂ), IsContRep B F f → IsContRep B F' f' → IsContRep B (F + c • F') (fun x => f x + c * f' x)) ∧ (∀ F f g, IsContRep B F f → IsContRep B (B.R g F) (fun x => f (x * g))) ∧ ∀ F f, IsContRep B F f → f =ᵐ[B.I.muA B.μf] B.I.ext F ∧ ∫⁻ x in B.fund, ‖f x‖ₑ ^ 2 ∂(B.I.muA B.μf) = ENNReal.ofReal (‖F‖ ^ 2) := by
  intro B
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro F f f' hf hf'
    exact ((GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.1 f' hf').symm
  · intro F F' f f' c hf hf'
    refine ⟨hf.1.add (continuous_const.mul hf'.1), ?_, ?_⟩
    · intro γ hγ x
      show f (γ * x) + c * f' (γ * x) = f x + c * f' x
      rw [hf.2.1 γ hγ x, hf'.2.1 γ hγ x]
    · filter_upwards [Lp.coeFn_add F (c • F'), Lp.coeFn_smul c F', hf.2.2, hf'.2.2]
        with x h1 h2 h3 h4
      rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4]
  · intro F f g hf
    exact (GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).2.2.1 g
  · intro F f hf
    refine ⟨(GlobalTheory.ExtContRep.ext_ae_eq_contRep B F f hf).1.symm, ?_⟩
    refine Eq.trans ?_ (lintegral_enorm_sq_eq ((B.I.muA B.μf).restrict B.fund) F)
    refine lintegral_congr_ae ?_
    filter_upwards [hf.2.2] with x hx
    rw [hx]

end GlobalTheory.ContRepUniq
