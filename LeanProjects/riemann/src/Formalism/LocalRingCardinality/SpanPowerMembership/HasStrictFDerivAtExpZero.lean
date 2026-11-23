import Mathlib

noncomputable section

namespace Formalism.BasicNotions.Examples₂.CD

open Filter Topology Metric NormedSpace Asymptotics

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

theorem hasStrictFDerivAt_exp_zero_alt : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
    ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) 0 := by
  have h := hasStrictFDerivAt_exp_zero (𝕂 := ℝ) (𝔸 := 𝔸)
  exact h

variable (𝔸) in

def logA : 𝔸 → 𝔸 := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse _ _ _

theorem logA_exp : ∀ᶠ X in 𝓝 (0 : 𝔸), logA 𝔸 (exp X) = X := hasStrictFDerivAt_exp_zero_alt.eventually_left_inverse

theorem exp_logA : ∀ᶠ h in 𝓝 (1 : 𝔸), exp (logA 𝔸 h) = h := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).eventually_right_inverse
  rw [exp_zero] at h
  exact h

theorem logA_one : logA 𝔸 (1 : 𝔸) = 0 := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).localInverse_apply_image
  rw [exp_zero] at h
  exact h

theorem hasStrict_logA : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸) (1 : 𝔸) := by
  have h := (hasStrictFDerivAt_exp_zero_alt (𝔸 := 𝔸)).to_localInverse
  rw [exp_zero] at h
  exact h

theorem exp_cont : Continuous (exp : 𝔸 → 𝔸) := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  exact NormedSpace.exp_continuous

theorem exp_neg_mul (X : 𝔸) : exp (-X) * exp X = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_left (Commute.refl X)), neg_add_cancel, exp_zero]

theorem exp_mul_neg (X : 𝔸) : exp X * exp (-X) = 1 := by
  letI : NormedAlgebra ℚ 𝔸 := NormedAlgebra.restrictScalars ℚ ℝ 𝔸
  rw [← exp_add_of_commute (Commute.neg_right (Commute.refl X)), add_neg_cancel, exp_zero]

def F1 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))

def F2 (p : 𝔸 × 𝔸) : 𝔸 := logA 𝔸 (exp p.1 * exp p.2)

theorem hasStrict_exp_comp (L : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => exp (L p)) L (0 : 𝔸 × 𝔸) := by
  have h0 : HasStrictFDerivAt (exp : 𝔸 → 𝔸)
      ((ContinuousLinearEquiv.refl ℝ 𝔸 : 𝔸 ≃L[ℝ] 𝔸) : 𝔸 →L[ℝ] 𝔸) (L 0) := by
    rw [map_zero]
    exact hasStrictFDerivAt_exp_zero_alt
  have h := h0.comp (0 : 𝔸 × 𝔸) L.hasStrictFDerivAt
  simpa using h

theorem hasStrict_mul (L M : 𝔸 × 𝔸 →L[ℝ] 𝔸) :
    HasStrictFDerivAt (fun p : 𝔸 × 𝔸 => logA 𝔸 (exp (L p) * exp (M p))) (L + M) (0 : 𝔸 × 𝔸) := by
  have hprod := (hasStrict_exp_comp L).mul' (hasStrict_exp_comp M)
  simp only [map_zero, exp_zero, one_smul, MulOpposite.op_one] at hprod
  have hlog : HasStrictFDerivAt (logA 𝔸) (ContinuousLinearMap.id ℝ 𝔸)
      (((fun p : 𝔸 × 𝔸 => exp (L p)) * fun p : 𝔸 × 𝔸 => exp (M p)) 0) := by
    simp only [Pi.mul_apply, map_zero, exp_zero, mul_one]
    exact hasStrict_logA
  have h := hlog.comp (0 : 𝔸 × 𝔸) hprod
  rw [ContinuousLinearMap.id_comp, add_comm] at h
  exact h

theorem hasStrictFDerivAt_translateLog : HasStrictFDerivAt (F1 (𝔸 := 𝔸)) (ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := by
  have h := hasStrict_mul (𝔸 := 𝔸) (-ContinuousLinearMap.fst ℝ 𝔸 𝔸)
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸)
  rw [neg_add_cancel_left] at h
  have hf : F1 (𝔸 := 𝔸) = fun p => logA 𝔸 (exp ((-ContinuousLinearMap.fst ℝ 𝔸 𝔸) p) *
      exp ((ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) p)) := by
    funext p
    simp [F1]
  rw [hf]
  exact h

theorem hasStrictFDerivAt_productLog : HasStrictFDerivAt (F2 (𝔸 := 𝔸))
    (ContinuousLinearMap.fst ℝ 𝔸 𝔸 + ContinuousLinearMap.snd ℝ 𝔸 𝔸) 0 := hasStrict_mul (ContinuousLinearMap.fst ℝ 𝔸 𝔸) (ContinuousLinearMap.snd ℝ 𝔸 𝔸)

theorem eventually_pair {P : 𝔸 × 𝔸 → Prop} (h : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), P p) :
    ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ → P (X, Y) := by
  obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X Y hX hY => hP ?_⟩
  rw [dist_zero_right, Prod.norm_def]
  exact max_lt hX hY

theorem strict_est {F : 𝔸 × 𝔸 → 𝔸} {F' : 𝔸 × 𝔸 →L[ℝ] 𝔸} (hF : HasStrictFDerivAt F F' 0)
    {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
      ‖F (X, Y) - F (X, 0) - F' (0, Y)‖ ≤ ε * ‖Y‖ := by
  have h := hF.isLittleO.def hε
  obtain ⟨δ, hδ, hq⟩ := Metric.eventually_nhds_iff.1 h
  refine ⟨δ, hδ, fun X Y hX hY => ?_⟩
  have hd : dist ((X, Y), (X, (0 : 𝔸))) ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) < δ := by
    rw [dist_eq_norm]
    have e : ((X, Y), (X, (0 : 𝔸))) - ((0 : 𝔸 × 𝔸), (0 : 𝔸 × 𝔸)) = ((X, Y), (X, 0)) := by simp
    rw [e, Prod.norm_def, Prod.norm_def, Prod.norm_def]
    simp only [norm_zero]
    exact max_lt (max_lt hX hY) (max_lt hX hδ)
  have h1 := hq hd
  beta_reduce at h1
  have e2 : ((X, Y) - (X, 0) : 𝔸 × 𝔸) = (0, Y) := by simp
  rw [e2, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at h1
  exact h1

theorem distortion {ε : ℝ} (hε : 0 < ε) : ∃ δ > 0, ∀ X Y : 𝔸, ‖X‖ < δ → ‖Y‖ < δ →
    (exp (F1 (X, Y)) = exp (-X) * exp (X + Y) ∧ ‖F1 (X, Y) - Y‖ ≤ ε * ‖Y‖) ∧
    (exp (F2 (X, Y)) = exp X * exp Y ∧ ‖F2 (X, Y) - X - Y‖ ≤ ε * ‖Y‖) := by
  have hc1 : Continuous (fun p : 𝔸 × 𝔸 => exp (-p.1) * exp (p.1 + p.2)) :=
    (exp_cont.comp continuous_fst.neg).mul (exp_cont.comp (continuous_fst.add continuous_snd))
  have hc2 : Continuous (fun p : 𝔸 × 𝔸 => exp p.1 * exp p.2) :=
    (exp_cont.comp continuous_fst).mul (exp_cont.comp continuous_snd)
  have e1 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸),
      exp (logA 𝔸 (exp (-p.1) * exp (p.1 + p.2))) = exp (-p.1) * exp (p.1 + p.2) := by
    have ht := hc1.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, neg_zero, add_zero, exp_zero, mul_one] at ht
    exact ht.eventually exp_logA
  have e2 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), exp (logA 𝔸 (exp p.1 * exp p.2)) = exp p.1 * exp p.2 := by
    have ht := hc2.tendsto 0
    simp only [Prod.fst_zero, Prod.snd_zero, exp_zero, mul_one] at ht
    exact ht.eventually exp_logA
  have e3 : ∀ᶠ p in 𝓝 (0 : 𝔸 × 𝔸), logA 𝔸 (exp p.1) = p.1 := by
    have ht := (continuous_fst (X := 𝔸) (Y := 𝔸)).tendsto 0
    simp only [Prod.fst_zero] at ht
    exact ht.eventually logA_exp
  obtain ⟨δ1, hδ1, h1⟩ := eventually_pair (e1.and (e2.and e3))
  obtain ⟨δ2, hδ2, h2⟩ := strict_est (hasStrictFDerivAt_translateLog (𝔸 := 𝔸)) hε
  obtain ⟨δ3, hδ3, h3⟩ := strict_est (hasStrictFDerivAt_productLog (𝔸 := 𝔸)) hε
  refine ⟨min δ1 (min δ2 δ3), lt_min hδ1 (lt_min hδ2 hδ3), fun X Y hX hY => ?_⟩
  have hX1 : ‖X‖ < δ1 := lt_of_lt_of_le hX (min_le_left _ _)
  have hY1 : ‖Y‖ < δ1 := lt_of_lt_of_le hY (min_le_left _ _)
  have hX2 : ‖X‖ < δ2 := lt_of_lt_of_le hX ((min_le_right _ _).trans (min_le_left _ _))
  have hY2 : ‖Y‖ < δ2 := lt_of_lt_of_le hY ((min_le_right _ _).trans (min_le_left _ _))
  have hX3 : ‖X‖ < δ3 := lt_of_lt_of_le hX ((min_le_right _ _).trans (min_le_right _ _))
  have hY3 : ‖Y‖ < δ3 := lt_of_lt_of_le hY ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨k1, k2, k3⟩ := h1 X Y hX1 hY1
  refine ⟨⟨k1, ?_⟩, ⟨k2, ?_⟩⟩
  · have h := h2 X Y hX2 hY2
    have hz : F1 (X, (0 : 𝔸)) = 0 := by
      simp only [F1, add_zero, exp_neg_mul, logA_one]
    rw [hz, sub_zero] at h
    simpa using h
  · have h := h3 X Y hX3 hY3
    have hz : F2 (X, (0 : 𝔸)) = X := by
      simp only [F2, exp_zero, mul_one]
      exact k3
    rw [hz] at h
    simpa using h

end Formalism.BasicNotions.Examples₂.CD
