import Formalism.UnipotentAdelicQuotients.EllRegStep
import Formalism.UnipotentAdelicQuotients.EllipticRegularity.BaseLevel

namespace ZetaZeros.D.EllReg

open MeasureTheory Metric Filter Topology
open scoped ContDiff FourierTransform ENNReal

lemma om_nonneg {d : ℕ} (s M ε : ℝ) (ξ : E d) : 0 ≤ om s M ε ξ := by
  unfold om
  exact mul_nonneg (Real.rpow_nonneg (add_nonneg zero_le_one (sq_nonneg _)) _)
    (Real.rpow_nonneg (add_nonneg zero_le_one (mul_nonneg (sq_nonneg _) (sq_nonneg _))) _)

lemma om_continuous_eps {d : ℕ} (s M : ℝ) (ξ : E d) : Continuous fun ε : ℝ => om s M ε ξ := by
  unfold om
  exact continuous_const.mul
    ((continuous_const.add ((continuous_pow 2).mul continuous_const)).rpow_const
      fun ε => Or.inl (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (sq_nonneg _) (sq_nonneg _))).ne')

lemma om_eps_zero {d : ℕ} (s M : ℝ) (ξ : E d) : om s M 0 ξ = om s 0 0 ξ := by
  unfold om
  simp

lemma om_continuous {d : ℕ} (s M ε : ℝ) : Continuous fun ξ : E d => om s M ε ξ := by
  unfold om
  exact ((continuous_const.add (continuous_norm.pow 2)).rpow_const
      fun ξ => Or.inl (add_pos_of_pos_of_nonneg one_pos (sq_nonneg _)).ne').mul
    ((continuous_const.add (continuous_const.mul (continuous_norm.pow 2))).rpow_const
      fun ξ => Or.inl (add_pos_of_pos_of_nonneg one_pos (mul_nonneg (sq_nonneg _) (sq_nonneg _))).ne')

theorem weightedNormLimit : EpsLimit := by
  unfold EpsLimit
  intro d s M F B hM hF hB
  unfold nrm at hB ⊢
  have he0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hpos : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have hle1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hlim : ∀ ξ : E d, Tendsto
      (fun n : ℕ => ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop
      (𝓝 (ENNReal.ofReal (om s 0 0 ξ) ^ 2 * ‖F ξ‖ₑ ^ 2)) := by
    intro ξ
    have h1 : Tendsto (fun n : ℕ => om s M (1 / ((n : ℝ) + 1)) ξ) atTop
        (𝓝 (om s 0 0 ξ)) := by
      rw [← om_eps_zero s M ξ]
      exact ((om_continuous_eps s M ξ).tendsto 0).comp he0
    have h2 : Tendsto (fun n : ℕ => ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2) atTop
        (𝓝 (ENNReal.ofReal (om s 0 0 ξ) ^ 2)) := by
      exact ((ENNReal.continuous_pow 2).tendsto _).comp ((ENNReal.continuous_ofReal.tendsto _).comp h1)
    have hfin : ‖F ξ‖ₑ ^ 2 ≠ ⊤ := ENNReal.pow_ne_top enorm_ne_top
    exact ENNReal.Tendsto.mul_const h2 (Or.inr hfin)
  have hmeas : ∀ n : ℕ, Measurable fun ξ : E d =>
      ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2 := fun n => by
    have hc := om_continuous (d := d) s M (1 / ((n : ℝ) + 1))
    exact ((ENNReal.measurable_ofReal.comp hc.measurable).pow_const 2).mul
      (hF.measurable.enorm.pow_const 2)
  calc ∫⁻ ξ, ENNReal.ofReal (om s 0 0 ξ) ^ 2 * ‖F ξ‖ₑ ^ 2
      = ∫⁻ ξ, liminf (fun n : ℕ =>
          ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop :=
        lintegral_congr fun ξ => ((hlim ξ).liminf_eq).symm
    _ ≤ liminf (fun n : ℕ => ∫⁻ ξ,
          ENNReal.ofReal (om s M (1 / ((n : ℝ) + 1)) ξ) ^ 2 * ‖F ξ‖ₑ ^ 2) atTop :=
        lintegral_liminf_le hmeas
    _ ≤ B := by
        refine Filter.liminf_le_of_le (by isBoundedDefault) fun b hb => ?_
        obtain ⟨n, hn⟩ := hb.exists
        exact hn.trans (hB _ (hpos n) (hle1 n))

private theorem rpow_le_rpow_of_le_of_exponent_nonpos {x y z : ℝ} (hx : 0 < x) (hxy : x ≤ y) (hz : z ≤ 0) :
    y ^ z ≤ x ^ z := by
  exact Real.rpow_le_rpow_of_nonpos hx hxy hz

private theorem sq_one_add_rpow_mul_rpow_le_max_mul_rpow (s M ε t : ℝ) (hε : 0 < ε) (ht : 0 ≤ t) :
    ((1 + t) ^ (s / 2) * (1 + ε ^ 2 * t) ^ (-(M / 2))) ^ 2 ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (s - M) := by
  have hA : 0 < 1 + t := by linarith
  have hε2 : 0 < ε ^ 2 := by positivity
  have hB : 0 < 1 + ε ^ 2 * t := add_pos_of_pos_of_nonneg one_pos (mul_nonneg hε2.le ht)
  have ha : 0 < min 1 (ε ^ 2) := lt_min one_pos hε2
  have hb : 0 < max 1 (ε ^ 2) := lt_of_lt_of_le one_pos (le_max_left _ _)
  have h1 : ((1 + t) ^ (s / 2)) ^ 2 = (1 + t) ^ s := by
    rw [sq ((1 + t) ^ (s / 2)), ← Real.rpow_add hA]
    congr 1
    ring
  have h2 : ((1 + ε ^ 2 * t) ^ (-(M / 2))) ^ 2 = (1 + ε ^ 2 * t) ^ (-M) := by
    rw [sq ((1 + ε ^ 2 * t) ^ (-(M / 2))), ← Real.rpow_add hB]
    congr 1
    ring
  have hAp : 0 ≤ (1 + t) ^ (-M) := Real.rpow_nonneg hA.le _
  have key : (1 + ε ^ 2 * t) ^ (-M) ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) := by
    rcases le_total 0 M with hM | hM
    · have hle : min 1 (ε ^ 2) * (1 + t) ≤ 1 + ε ^ 2 * t := by
        have e1 : min 1 (ε ^ 2) ≤ 1 := min_le_left _ _
        have e2 : min 1 (ε ^ 2) * t ≤ ε ^ 2 * t := mul_le_mul_of_nonneg_right (min_le_right _ _) ht
        nlinarith
      calc (1 + ε ^ 2 * t) ^ (-M) ≤ (min 1 (ε ^ 2) * (1 + t)) ^ (-M) :=
            rpow_le_rpow_of_le_of_exponent_nonpos (mul_pos ha hA) hle (by linarith)
        _ = (min 1 (ε ^ 2)) ^ (-M) * (1 + t) ^ (-M) := Real.mul_rpow ha.le hA.le
        _ ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hAp
    · have hle : 1 + ε ^ 2 * t ≤ max 1 (ε ^ 2) * (1 + t) := by
        have e1 : 1 ≤ max 1 (ε ^ 2) := le_max_left _ _
        have e2 : ε ^ 2 * t ≤ max 1 (ε ^ 2) * t := mul_le_mul_of_nonneg_right (le_max_right _ _) ht
        nlinarith
      calc (1 + ε ^ 2 * t) ^ (-M) ≤ (max 1 (ε ^ 2) * (1 + t)) ^ (-M) :=
            Real.rpow_le_rpow hB.le hle (by linarith)
        _ = (max 1 (ε ^ 2)) ^ (-M) * (1 + t) ^ (-M) := Real.mul_rpow hb.le hA.le
        _ ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M) :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) hAp
  rw [mul_pow, h1, h2, sub_eq_add_neg, Real.rpow_add hA]
  calc (1 + t) ^ s * (1 + ε ^ 2 * t) ^ (-M)
      ≤ (1 + t) ^ s * (max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + t) ^ (-M)) :=
        mul_le_mul_of_nonneg_left key (Real.rpow_nonneg hA.le _)
    _ = max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * ((1 + t) ^ s * (1 + t) ^ (-M)) := by
        ring

lemma om_sq_le {d : ℕ} (s M ε : ℝ) (hε : 0 < ε) (ξ : E d) :
    om s M ε ξ ^ 2 ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + ‖ξ‖ ^ 2) ^ (s - M) := by
  unfold om
  exact sq_one_add_rpow_mul_rpow_le_max_mul_rpow s M ε _ hε (by positivity)

theorem weightedNormFinite : FiniteWeighted := by
  unfold FiniteWeighted
  intro d g hg hgc s M ε hε hsM
  unfold nrm
  have hint0 : Integrable (fun ξ : E d => ((1 : ℝ) + ‖ξ‖ ^ 2) ^ (-(2 * (M - s)) / 2)) := by
    apply integrable_rpow_neg_one_add_norm_sq
    rw [finrank_euclideanSpace_fin]
    linarith
  have hexp : -(2 * (M - s)) / 2 = s - M := by ring
  rw [hexp] at hint0
  have hint_r := (hint0.const_mul (max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)))).mul_const
    ((∫ x, ‖g x‖) ^ 2)
  refine lt_of_le_of_lt (lintegral_mono fun ξ => ?_) hint_r.lintegral_lt_top
  have hK : 0 ≤ max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) :=
    le_max_of_le_right (Real.rpow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
  have hw := om_nonneg s M ε ξ
  have hreal : om s M ε ξ ^ 2 * ‖𝓕 g ξ‖ ^ 2 ≤
      max ((min 1 (ε ^ 2)) ^ (-M)) ((max 1 (ε ^ 2)) ^ (-M)) * (1 + ‖ξ‖ ^ 2) ^ (s - M) *
        (∫ x, ‖g x‖) ^ 2 := by
    refine mul_le_mul (om_sq_le s M ε hε ξ) ?_ (sq_nonneg _)
      (mul_nonneg hK (Real.rpow_nonneg (by positivity) _))
    rw [sq, sq]
    exact mul_self_le_mul_self (norm_nonneg _) (norm_fourier_le_integral_norm g ξ)
  have heq : ENNReal.ofReal (om s M ε ξ) ^ 2 * ‖𝓕 g ξ‖ₑ ^ 2 =
      ENNReal.ofReal (om s M ε ξ ^ 2 * ‖𝓕 g ξ‖ ^ 2) := by
    rw [ENNReal.ofReal_mul (sq_nonneg _), ENNReal.ofReal_pow hw, ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm]
  exact heq.trans_le (ENNReal.ofReal_le_ofReal hreal)

end ZetaZeros.D.EllReg
