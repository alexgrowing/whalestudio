import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BridgeOrbVecAt

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions

namespace Formalism.L2.SG.Pf.Bridge

section Scale

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq]

theorem isNormCut_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    {c : ℝ} (hc : 0 < c) (θ : Formalism.FourierDecayAlt.B.SS k r → ℝ) :
    Formalism.FourierDecayAlt.D.IsNormCut D γ (ENNReal.ofReal c • μ) θ ↔ Formalism.FourierDecayAlt.D.IsNormCut D γ μ (fun p => c * θ p) := by
  unfold Formalism.FourierDecayAlt.D.IsNormCut
  have hint : ∀ p, ∫ x, θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) ∂(ENNReal.ofReal c • μ) =
      ∫ x, c * θ (Formalism.FourierDecayAlt.C6.actR γ (Matrix.of x) p) ∂μ := fun p => by
    rw [integral_smul_measure, ENNReal.toReal_ofReal hc.le, integral_const_mul, smul_eq_mul]
  simp only [hint]
  constructor
  · rintro ⟨hm, hpos, hone⟩
    exact ⟨hm.const_mul c, fun p => mul_nonneg hc.le (hpos p), hone⟩
  · rintro ⟨hm, hpos, hone⟩
    refine ⟨?_, fun p => ?_, hone⟩
    · have : θ = fun p => c⁻¹ * (c * θ p) := by funext p; field_simp
      rw [this]; exact hm.const_mul _
    · exact (mul_nonneg_iff_of_pos_left hc).mp (hpos p)

theorem orbJ_smul (D : Formalism.FourierDecayAlt.B.RealPlaceData k r Wp Wq) (γ : Formalism.FourierDecayAlt.B.Mat k r) (μ : Measure (Formalism.QuantumDeterminants.Mt k r))
    (F : Formalism.FourierDecayAlt.B.Mat k r → (Wq →L[ℂ] Wp)) (hrel : Formalism.FourierDecayAlt.C6.IsRelevant D γ)
    (hH : Formalism.FourierDecayAlt.B.IsHaarOn (Formalism.FourierDecayAlt.C6.Rset γ) μ) {c : ℝ} (hc : 0 < c) :
    Formalism.FourierDecayAlt.D.orbJ D γ (ENNReal.ofReal c • μ) F = ((c⁻¹ : ℝ) : ℂ) • Formalism.FourierDecayAlt.D.orbJ D γ μ F := by
  unfold Formalism.FourierDecayAlt.D.orbJ
  by_cases h1 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ (ENNReal.ofReal c • μ) θ ∧
      Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS
  · have hc1 := (isNormCut_smul D γ μ hc _).mp h1.choose_spec.1
    have hi1 : Integrable (fun p => (c * h1.choose p) • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
      simp only [mul_smul]; exact h1.choose_spec.2.smul c
    have h2 : ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := ⟨_, hc1, hi1⟩
    rw [dif_pos h1, dif_pos h2]
    have hind := Formalism.FourierDecayAlt.P.orbital_integral_indep_choice k r Wp Wq D γ μ hrel hH F h2.choose (fun p => c * h1.choose p)
      h2.choose_spec.1 hc1 h2.choose_spec.2 hi1
    rw [hind]
    simp only [mul_smul]
    rw [integral_smul, ← Complex.coe_smul c, smul_smul, ← Complex.ofReal_mul, inv_mul_cancel₀ hc.ne',
      Complex.ofReal_one, one_smul]
  · have h2 : ¬ ∃ θ, Formalism.FourierDecayAlt.D.IsNormCut D γ μ θ ∧
        Integrable (fun p => θ p • Formalism.FourierDecayAlt.D.orbIntegrand D γ F p) D.μSS := by
      rintro ⟨θ, hθ, hi⟩
      apply h1
      refine ⟨fun p => c⁻¹ * θ p, (isNormCut_smul D γ μ hc _).mpr ?_, ?_⟩
      · have : (fun p => c * (c⁻¹ * θ p)) = θ := by funext p; field_simp
        rw [this]; exact hθ
      · simp only [mul_smul]; exact hi.smul c⁻¹
    rw [dif_neg h1, dif_neg h2, smul_zero]

end Scale

end Formalism.L2.SG.Pf.Bridge
