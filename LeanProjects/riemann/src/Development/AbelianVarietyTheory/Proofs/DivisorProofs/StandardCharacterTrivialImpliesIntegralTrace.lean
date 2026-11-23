import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMulIntSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThetaDenom
open scoped TensorProduct NNReal Matrix

namespace GlobalTheory.TraceIntStd

theorem trace_int_of_isStd : ∀ {F : Type} [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ x : F,
    (∀ t : AF F, t.1 = 0 → (∀ v, ‖evFin F v t‖ ≤ 1) → ψ (algebraMap F (AF F) x * t) = 1) →
    ∃ z : ℤ, Algebra.trace ℚ F x = z := by
  intro F _ _ ψ hψ x h
  have h1 := h (pairA F 0 1) rfl (fun v => by
    show ‖Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v (sndA F (pairA F 0 1))‖ ≤ 1
    rw [show sndA F (pairA F 0 1) = 1 from rfl, map_one, norm_one])
  have e : algebraMap F (AF F) x * pairA F 0 1 = pairA F 0 (algebraMap F (Af F) x) := by
    refine Prod.ext ?_ ?_
    · show algebraMap F (Ainf F) x * 0 = 0
      exact mul_zero _
    · show algebraMap F (Af F) x * 1 = algebraMap F (Af F) x
      exact mul_one _
  rw [e, GlobalTheory.PsiNontriv.isStd_fin_rat hψ, Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  refine ⟨n, ?_⟩
  have hne : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have h2 : ((Algebra.trace ℚ F x : ℚ) : ℂ) = ((n : ℚ) : ℂ) := by
    have := hn
    rw [mul_comm (2 * Real.pi * Complex.I : ℂ)] at this
    push_cast
    exact mul_right_cancel₀ hne this
  exact_mod_cast h2

end GlobalTheory.TraceIntStd
