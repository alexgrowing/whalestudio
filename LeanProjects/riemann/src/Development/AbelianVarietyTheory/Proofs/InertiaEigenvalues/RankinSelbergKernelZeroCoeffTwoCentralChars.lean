import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOfMemSmoothSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRapidInf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNormRsHatLeConst
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaIntegralUpperMspan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousIntegralOfCompact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SetIntegralRsHatZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspFormRapidKernelSmoothSpanSmoothCuspidalBound
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CuspRep GlobalTheory.UnitaryBC GroundTheory.Global.IdeleGroup Formalism.L2.Host
open scoped nonZeroDivisors ComplexConjugate

open GlobalTheory.ThetaPoisson GlobalTheory.RSTheta GlobalTheory.Petersson GlobalTheory.CuspQuot GlobalTheory.RSThetaLow GroundTheory.Automorphic.GJMatrix

noncomputable section

namespace GlobalTheory.RSResidue

theorem rsHat_zero_props_two : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ω ω' : HChar E), ω.IsUnitary → ω'.IsUnitary → ∀ (φ φ' : Sm E a), φ.1 ∈ GlobalTheory.Petersson.bddForms E a ω → φ'.1 ∈ GlobalTheory.Petersson.bddForms E a ω' → ∀ (ℓ : Fin a) (Φ : (Fin a → Cinf E) → ℂ), GlobalTheory.CuspQuot.IsTest (GlobalTheory.RSTheta.rowSet E ℓ) Φ → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (η : Fin a → Af E), Continuous (fun g => GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ (∃ C : ℝ, ∀ g, ‖GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0‖ ≤ C) ∧ (∀ (γ : GL (Fin a) E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) 0 = GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0) ∧ ∀ (z : Neutral.B1.Ideles E) (g : GA E a), GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η (GeneralLinearGroup.scalar (Fin a) z * g) 0 = ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * GlobalTheory.RSThetaLow.rsHat ℓ φ.1 φ'.1 Φ J η g 0 := by
  intro E _ _ _ a ω ω' hω hω' φ φ' h h' ℓ Φ hΦ J η
  obtain ⟨c, hc⟩ := rsHat_zero_eq J η φ φ' hΦ
  have hc' : ∀ g, rsHat ℓ φ.1 φ'.1 Φ J η g 0 = (∫ u, rsInf ℓ φ.1 φ'.1 Φ g u ∂infMeasure E a) * c := hc
  have hj : Continuous fun p : GA E a × (Fin a → Cinf E) => rsInf ℓ φ.1 φ'.1 Φ p.1 p.2 :=
    continuous_rsInf h.1 h'.1 hΦ.1.continuous hΦ.2.2
  have h0 : ∀ g, ∀ u ∉ tsupport Φ, rsInf ℓ φ.1 φ'.1 Φ g u = 0 := fun g u hu => by
    rw [rsInf, image_eq_zero_of_notMem_tsupport hu, mul_zero]
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [hc']
    exact (continuous_integral_of_compact (infMeasure E a) hΦ.2.1 hj h0).mul continuous_const
  · obtain ⟨C, hC⟩ := h.2.2.2
    obtain ⟨C', hC'⟩ := h'.2.2.2
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 1)
    have hi : Integrable (fun u => C * C' * ‖Φ u‖) (infMeasure E a) :=
      (integrable_infMeasure hΦ.1.continuous hΦ.2.1).norm.const_mul _
    refine ⟨(∫ u, C * C' * ‖Φ u‖ ∂infMeasure E a) * ‖c‖, fun g => ?_⟩
    rw [hc', norm_mul]
    refine mul_le_mul_of_nonneg_right (norm_integral_le_of_norm_le hi (.of_forall fun u => ?_)) (norm_nonneg _)
    rw [rsInf, norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_right (mul_le_mul (hC _) (hC' _) (norm_nonneg _) hC0) (norm_nonneg _)
  · intro γ g
    have e : rsPsi ℓ φ.1 φ'.1 Φ J η (ratGL E a γ * g) = rsPsi ℓ φ.1 φ'.1 Φ J η g := funext fun y =>
      rsPsi_ratGL_mul ℓ h.2.1 h'.2.1 Φ J η γ g y
    simp only [rsHat, e]
  · intro z g
    have e : ∀ u, rsInf ℓ φ.1 φ'.1 Φ (GeneralLinearGroup.scalar (Fin a) z * g) u =
        ((ω.1 z : ℂˣ) : ℂ) * starRingEnd ℂ ((ω'.1 z : ℂˣ) : ℂ) * rsInf ℓ φ.1 φ'.1 Φ g u := fun u => by
      simp only [rsInf, mul_assoc (GeneralLinearGroup.scalar (Fin a) z) g, h.2.2.1, h'.2.2.1, map_mul]
      ring
    rw [hc', hc', funext e, integral_const_mul]
    ring

end GlobalTheory.RSResidue
