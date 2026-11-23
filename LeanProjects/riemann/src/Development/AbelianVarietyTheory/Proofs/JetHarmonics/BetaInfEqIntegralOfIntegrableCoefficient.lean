import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegrandAestronglyMeasurable

noncomputable section

namespace GlobalTheory.RegularisedIntegral

section

open Matrix MeasureTheory Filter Topology
open scoped ENNReal
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B6

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem dilate_subst (D : RealPlaceData k r Wp Wq) {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : SS k r → E} (hf : Integrable f D.μSS) {t : ℝ × ℝ} (h1 : 0 < t.1) (h2 : 0 < t.2) :
    Integrable (fun p => f (dilation₂ t p)) D.μSS ∧
      (∫ p, f (dilation₂ t p) ∂D.μSS) = ((t.1 * t.2) ^ kap k r)⁻¹ • ∫ p, f p ∂D.μSS := by
  have hm := map_measure_dilation_pair_eq_smul (dilation_jacobian_every_setting k r Wp Wq D) h1 h2
  have hf' : Integrable f (D.μSS.map (dilation₂ t)) := by
    rw [hm]
    exact hf.smul_measure (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
  refine ⟨hf'.comp_measurable (dilation_action_measurable t), ?_⟩
  rw [← integral_map (dilation_action_measurable t).aemeasurable hf'.1, hm, integral_smul_measure, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity), mul_pow, mul_inv]

def kernel (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) (q : SS k r × (ℝ × ℝ)) : ℂ :=
  Bt D F F' q * Complex.exp (Complex.I * (phase D τ q.1 q.2 : ℂ))

variable {D : RealPlaceData k r Wp Wq} {α : ℝ}

theorem betaInfTau_eq_kernel (H : SqIntegrable D α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} {c c' : ℝ}
    (hF : AdmW α c 2 2 F) (hF' : AdmW α c' 2 2 F') (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, (∫ t : ℝ × ℝ, kernel D F F' τ (p, t)) ∂D.μSS := by
  unfold betaInfTau
  refine integral_congr_ae ?_
  filter_upwards [ae_inSS D] with p hp
  have key := (bracket_calculus H hF hF' hp).2.2.2 (τ.1 * lam k r D.z (Matrix.of p.1.2))
    (-(τ.2 * lam k r D.z' (Matrix.of p.2.2)))
  have e : ∀ t : ℝ × ℝ, τ.1 * t.1 * lam k r D.z (Matrix.of p.1.2) - τ.2 * t.2 * lam k r D.z' (Matrix.of p.2.2) =
      τ.1 * lam k r D.z (Matrix.of p.1.2) * t.1 + -(τ.2 * lam k r D.z' (Matrix.of p.2.2)) * t.2 := fun t => by ring
  simp only [kernel, phase, Bt_eq D F F' hp, e]
  rw [key, ← mul_assoc, ← Complex.ofReal_mul]
  have : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2)⁻¹ * (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2)⁻¹ *
      ((1 + (τ.1 * lam k r D.z (Matrix.of p.1.2)) ^ 2) *
        (1 + (-(τ.2 * lam k r D.z' (Matrix.of p.2.2))) ^ 2)) = 1 := by
    have a1 : (1 + τ.1 ^ 2 * lam k r D.z (Matrix.of p.1.2) ^ 2) ≠ 0 := by positivity
    have a2 : (1 + τ.2 ^ 2 * lam k r D.z' (Matrix.of p.2.2) ^ 2) ≠ 0 := by positivity
    field_simp
  rw [this]
  simp

theorem kernel_slice (D : RealPlaceData k r Wp Wq) (F F' : Mat k r → (Wq →L[ℂ] Wp)) (τ : ℝ × ℝ) {t : ℝ × ℝ}
    (h1 : 0 < t.1) (h2 : 0 < t.2) :
    (fun p => kernel D F F' τ (p, t)) =ᵐ[D.μSS] fun p =>
      (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ) • (xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)) := by
  filter_upwards [ae_inSS D] with p hp
  obtain ⟨l1, l2⟩ := lam_dil dilation_unipotent_measure D hp h1 h2
  have l1' : lam k r D.z (Matrix.of (dilation₂ t p).1.2) = t.1 * lam k r D.z (Matrix.of p.1.2) := l1
  have l2' : lam k r D.z' (Matrix.of (dilation₂ t p).2.2) = t.2 * lam k r D.z' (Matrix.of p.2.2) := l2
  unfold kernel xiTau phase
  rw [Bt_eq D F F' hp, l1', l2', Complex.real_smul]
  unfold regBracket
  simp only [mul_assoc]
  ring

theorem kernel_slice_integral (D : RealPlaceData k r Wp Wq) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (τ : ℝ × ℝ)
    (hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS) (t : ℝ × ℝ) :
    Integrable (fun p => kernel D F F' τ (p, t)) D.μSS ∧
      (∫ p, kernel D F F' τ (p, t) ∂D.μSS) =
        ((D.χ t.1 * D.χ t.2 : ℝ) : ℂ) * ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS ∧
      (∫ p, ‖kernel D F F' τ (p, t)‖ ∂D.μSS) =
        |D.χ t.1| * |D.χ t.2| * ∫ p, ‖xiTau D τ p * Ph D F F' p‖ ∂D.μSS := by
  by_cases ht : t ∈ Set.Ioo (1 / 2 : ℝ) 2 ×ˢ Set.Ioo (1 / 2 : ℝ) 2
  · have h1 : 0 < t.1 := lt_trans (by norm_num) ht.1.1
    have h2 : 0 < t.2 := lt_trans (by norm_num) ht.2.1
    have e := kernel_slice D F F' τ h1 h2
    obtain ⟨i1, s1⟩ := dilate_subst D hf h1 h2
    obtain ⟨-, s2⟩ := dilate_subst D hf.norm h1 h2
    have hpos : 0 < (t.1 * t.2) ^ kap k r := by positivity
    refine ⟨(i1.smul (D.χ t.1 * D.χ t.2 * (t.1 * t.2) ^ kap k r : ℝ)).congr e.symm, ?_, ?_⟩
    · rw [integral_congr_ae e, integral_smul, s1, smul_smul, mul_assoc, mul_inv_cancel₀ hpos.ne', mul_one,
        Complex.real_smul]
    · have e' : (fun p => ‖kernel D F F' τ (p, t)‖) =ᵐ[D.μSS] fun p =>
          (|D.χ t.1| * |D.χ t.2| * (t.1 * t.2) ^ kap k r) * ‖xiTau D τ (dilation₂ t p) * Ph D F F' (dilation₂ t p)‖ := by
        filter_upwards [e] with p hp
        rw [hp, norm_smul, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hpos]
      rw [integral_congr_ae e', integral_const_mul, s2, smul_eq_mul, ← mul_assoc, mul_assoc _ _ (_⁻¹),
        mul_inv_cancel₀ hpos.ne', mul_one]
  · have hz : D.χ t.1 * D.χ t.2 = 0 := by
      by_cases h1 : t.1 ∈ Set.Ioo (1 / 2 : ℝ) 2
      · have h2 : t.2 ∉ Set.Ioo (1 / 2 : ℝ) 2 := fun h => ht ⟨h1, h⟩
        rw [cutoff_vanishes_outside_interval D h2, mul_zero]
      · rw [cutoff_vanishes_outside_interval D h1, zero_mul]
    have e : ∀ p, kernel D F F' τ (p, t) = 0 := fun p => by
      unfold kernel
      rw [Bt_zero D F F' p ht, zero_mul]
    rw [← abs_mul, hz]
    simp [e]

theorem betaInfTau_eq_integral (hα : AB k r ≤ α) {F F' : Mat k r → (Wq →L[ℂ] Wp)} (hcF : InCC α 4 F)
    (hcF' : InCC α 4 F') (hΦ : Integrable (Ph D F F') D.μSS) (τ : ℝ × ℝ) :
    betaInfTau D τ F F' = ∫ p, xiTau D τ p * Ph D F F' p ∂D.μSS := by
  obtain ⟨c, hc⟩ := hcF
  obtain ⟨c', hc'⟩ := hcF'
  have hF := admissible_weighted_of_bound hc
  have hF' := admissible_weighted_of_bound hc'
  have H := sqIntegrable_of_threshold D hα
  have := sigmaFinite_μSS D
  have hξ : Continuous (xiTau D τ) := by
    unfold xiTau
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul (first_eigenvalue_continuous D)).sub (continuous_const.mul (continuous_lambda_second_coordinate D)))))
  have hf : Integrable (fun p => xiTau D τ p * Ph D F F' p) D.μSS := by
    refine hΦ.norm.mono' (hξ.aestronglyMeasurable.mul hΦ.1) (Eventually.of_forall fun p => ?_)
    unfold xiTau
    rw [norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  have hs := kernel_slice_integral D τ hf
  have hmeas : AEStronglyMeasurable (kernel D F F' τ) (D.μSS.prod volume) := by
    unfold kernel
    refine ((cutBracket_measurable H hF hF').mul (Continuous.stronglyMeasurable ?_)).aestronglyMeasurable
    have hp : Continuous fun q : SS k r × (ℝ × ℝ) => phase D τ q.1 q.2 :=
      (phase_continuous D).comp ((continuous_const.prodMk continuous_fst).prodMk continuous_snd)
    exact Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp hp))
  have hχ : Integrable D.χ := by
    by_contra h
    have := D.χ_int
    rw [integral_undef h] at this
    exact zero_ne_one this
  have hK : Integrable (kernel D F F' τ) (D.μSS.prod volume) := by
    refine (integrable_prod_iff' hmeas).2 ⟨Eventually.of_forall fun t => (hs t).1, ?_⟩
    simp only [fun t => (hs t).2.2]
    refine Integrable.mul_const ?_ _
    rw [Measure.volume_eq_prod]
    exact hχ.abs.mul_prod hχ.abs
  rw [betaInfTau_eq_kernel H hF hF', integral_integral_swap (f := fun p t => kernel D F F' τ (p, t)) hK]
  simp only [fun t => (hs t).2.1]
  rw [integral_mul_const, integral_cutoff_product_eq_one, one_mul]

end

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem betaInf_eq_integral :
    ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
      [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq]
      [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (A : ℝ) (F : Mx k r → (Wq →L[ℂ] Wp)),
      B.AB k r ≤ A → B.InCC A 4 F → Integrable (B.Ph D F F) D.μSS →
      B.betaInf D F F = ∫ p, B.xiTau D (1, 1) p * B.Ph D F F p ∂D.μSS :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hA hF hΦ => betaInfTau_eq_integral hA hF hF hΦ (1, 1)

end GlobalTheory.RegularisedIntegral
