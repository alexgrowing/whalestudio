import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.ThetaConstantWeber
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.ThetaLine
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DifferentiableOddTheta
open Complex

open UpperHalfPlane hiding I
open scoped Real
open Filter Topology

noncomputable section

namespace GlobalTheory.ThetaWeberRoad.OddDeriv

def tailProd (τ : ℍ) (v : ℂ) : ℂ := ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ) * v)

lemma hasProd_tailProd (τ : ℍ) (v : ℂ) :
    HasProd (fun n : ℕ => 1 - ModularForm.eta_q n (τ : ℂ) * v) (tailProd τ v) := by
  have hs : Summable fun n : ℕ => ‖-(ModularForm.eta_q n (τ : ℂ) * v)‖ := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg, norm_mul] at h ⊢
    exact h.mul_right _
  have hm : Multipliable fun n : ℕ => 1 + -(ModularForm.eta_q n (τ : ℂ) * v) :=
    multipliable_one_add_of_summable hs
  simp only [← sub_eq_add_neg] at hm
  exact hm.hasProd

lemma continuousAt_tailProd (τ : ℍ) (v₀ : ℂ) : ContinuousAt (tailProd τ) v₀ := by
  have hK : IsCompact (Metric.closedBall v₀ 1) := isCompact_closedBall v₀ 1
  have hu : Summable fun n : ℕ => ‖ModularForm.eta_q n (τ : ℂ)‖ * (‖v₀‖ + 1) := by
    have h := ModularForm.summable_eta_q τ
    simp only [norm_neg] at h
    exact h.mul_right _
  have H := Summable.hasProdUniformlyOn_nat_one_add
    (f := fun n v => -(ModularForm.eta_q n (τ : ℂ) * v)) hK hu
    (Filter.Eventually.of_forall fun n v hv => by
      rw [norm_neg, norm_mul]
      exact mul_le_mul_of_nonneg_left (norm_le_of_mem_closedBall hv) (norm_nonneg _))
    (fun n => by fun_prop)
  rw [hasProdUniformlyOn_iff_tendstoUniformlyOn] at H
  have hc := H.continuousOn (Frequently.of_forall fun s =>
    (continuous_finsetProd s fun i _ => by fun_prop).continuousOn)
  have : ContinuousOn (tailProd τ) (Metric.closedBall v₀ 1) := by
    refine hc.congr fun v _ => ?_
    simp [tailProd, sub_eq_add_neg]
  exact this.continuousAt (Metric.closedBall_mem_nhds v₀ one_pos)

lemma tpFactor_shift (τ : ℍ) (z : ℂ) (n : ℕ) :
    tpFactor τ (z + ((τ : ℂ) + 1) / 2) n =
      (1 - ModularForm.eta_q n (τ : ℂ) * 1) *
        (1 - ModularForm.eta_q n (τ : ℂ) * cexp (2 * π * I * z)) *
        (1 - cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
  have hm : cexp (-(π * I)) = -1 := by rw [Complex.exp_neg, Complex.exp_pi_mul_I]; norm_num
  have hp : cexp (π * I) = -1 := Complex.exp_pi_mul_I
  have h1 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) + 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) := by
    rw [show -(cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z)) =
      cexp (2 * π * I * ((n : ℂ) + 1) * (τ : ℂ)) * cexp (2 * π * I * z) * cexp (π * I) by
        rw [hp]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  have h2 : cexp (π * I * (2 * (n : ℂ) + 1) * (τ : ℂ) - 2 * π * I * (z + ((τ : ℂ) + 1) / 2)) =
      -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) := by
    rw [show -(cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      cexp (2 * π * I * n * (τ : ℂ)) * cexp (-(2 * π * I * z)) * cexp (-(π * I)) by
        rw [hm]; ring, ← Complex.exp_add, ← Complex.exp_add]
    congr 1; ring
  unfold tpFactor
  rw [ModularForm.eta_q_eq_cexp, h1, h2]
  ring

lemma jacobiTheta₂_shift (hT : TripleProduct) (τ : ℍ) (z : ℂ) :
    jacobiTheta₂ (z + ((τ : ℂ) + 1) / 2) τ =
      tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
        ((1 - cexp (-(2 * π * I * z))) * tailProd τ (cexp (-(2 * π * I * z)))) := by
  have hA := hasProd_tailProd τ 1
  have hB := hasProd_tailProd τ (cexp (2 * π * I * z))
  have h0 := hasProd_tailProd τ (cexp (-(2 * π * I * z)))
  have h1 : HasProd (fun n : ℕ => 1 - cexp (2 * π * I * ((n + 1 : ℕ) : ℂ) * (τ : ℂ)) *
      cexp (-(2 * π * I * z))) (tailProd τ (cexp (-(2 * π * I * z)))) := by
    convert h0 using 2 with n
    rw [ModularForm.eta_q_eq_cexp]; push_cast; ring_nf
  have hC := HasProd.zero_mul
    (f := fun n : ℕ => 1 - cexp (2 * π * I * (n : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) h1
  have e0 : (1 - cexp (2 * π * I * ((0 : ℕ) : ℂ) * (τ : ℂ)) * cexp (-(2 * π * I * z))) =
      1 - cexp (-(2 * π * I * z)) := by simp
  rw [e0] at hC
  have hAll := (hA.mul hB).mul hC
  refine (hT τ (z + ((τ : ℂ) + 1) / 2)).unique ?_
  convert hAll using 1
  funext n
  rw [tpFactor_shift]

end GlobalTheory.ThetaWeberRoad.OddDeriv

namespace GlobalTheory.ThetaWeberRoad.OddDeriv

theorem hasDerivAt_mul_of_eq_zero {F R : ℂ → ℂ} {F' : ℂ} (hF : HasDerivAt F F' 0) (hF0 : F 0 = 0)
    (hR : ContinuousAt R 0) : HasDerivAt (fun z => F z * R z) (F' * R 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope] at hF ⊢
  have hR' : Tendsto R (𝓝[≠] (0 : ℂ)) (𝓝 (R 0)) := hR.tendsto.mono_left nhdsWithin_le_nhds
  refine (hF.mul hR').congr' ?_
  filter_upwards with z
  simp only [slope_def_field, hF0, sub_zero, zero_mul]
  ring

theorem hasDerivAt_oddTheta_zero :
    TripleProduct → ∀ τ : UpperHalfPlane,
      HasDerivAt (oddTheta τ) (-2 * (Real.pi : ℂ) * ModularForm.eta (τ : ℂ) ^ 3) 0 := by
  intro hT τ
  set F : ℂ → ℂ := fun z => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)) *
    (1 - cexp (-(2 * π * I * z))) with hFdef
  set R : ℂ → ℂ := fun z => tailProd τ 1 * tailProd τ (cexp (2 * π * I * z)) *
    tailProd τ (cexp (-(2 * π * I * z))) with hRdef
  have hfun : oddTheta τ = fun z => F z * R z := by
    funext z
    simp only [oddTheta, F, R]
    rw [jacobiTheta₂_shift hT]
    ring
  have hF0 : F 0 = 0 := by simp [F]
  have h1 : HasDerivAt (fun z : ℂ => cexp (π * I * (τ : ℂ) / 4 + π * I * (z + 1 / 2)))
      (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1)) 0 :=
    ((((hasDerivAt_id (0 : ℂ)).add_const (1 / 2)).const_mul (π * I)).const_add _).cexp
  have h2 : HasDerivAt (fun z : ℂ => 1 - cexp (-(2 * π * I * z)))
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1))) 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul (2 * π * I)).neg.cexp).const_sub 1
  have hF : HasDerivAt F (cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) * (π * I * 1) *
      (1 - cexp (-(2 * π * I * 0))) + cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) *
      (-(cexp (-(2 * π * I * 0)) * -(2 * π * I * 1)))) 0 := h1.mul h2
  have hR : ContinuousAt R 0 := by
    have hu : Continuous fun z : ℂ => cexp (2 * π * I * z) := by fun_prop
    have hv : Continuous fun z : ℂ => cexp (-(2 * π * I * z)) := by fun_prop
    exact (continuousAt_const.mul ((continuousAt_tailProd τ _).comp hu.continuousAt)).mul
      ((continuousAt_tailProd τ _).comp hv.continuousAt)
  rw [hfun]
  have key := hasDerivAt_mul_of_eq_zero hF hF0 hR
  convert key using 1
  have hT1 : tailProd τ 1 = ∏' n : ℕ, (1 - ModularForm.eta_q n (τ : ℂ)) := by
    simp [tailProd]
  have hq : (Function.Periodic.qParam 24 (τ : ℂ)) ^ 3 = cexp (π * I * (τ : ℂ) / 4) := by
    rw [Function.Periodic.qParam, ← Complex.exp_nat_mul]
    congr 1; push_cast; ring
  have hI : cexp (π * I * (τ : ℂ) / 4 + π * I * (0 + 1 / 2)) = cexp (π * I * (τ : ℂ) / 4) * I := by
    rw [Complex.exp_add]
    congr 1
    rw [show π * I * (0 + 1 / 2) = ((π / 2 : ℝ) : ℂ) * I by push_cast; ring, Complex.exp_mul_I]
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two, Real.sin_pi_div_two]
    simp
  simp only [R, mul_zero, neg_zero, Complex.exp_zero, hT1, hI]
  unfold ModularForm.eta
  rw [mul_pow, hq]
  ring_nf
  rw [Complex.I_sq]
  ring

end GlobalTheory.ThetaWeberRoad.OddDeriv
