import Formalism.LocalToGlobal.IndefiniteReal.GvPairOfOrbitDerivCont

noncomputable section

open MeasureTheory Matrix Metric Topology
open scoped ContDiff

namespace Formalism.IndefR.Eqv.KerDiag

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def qdist (m : Matrix (Fin n) (Fin n) ℂ) : ℝ :=
  ∑ i, ∑ j, ((m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).re ^ 2 + (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).im ^ 2)

theorem contDiff_entry (i j : Fin n) : ContDiff ℝ ∞ (fun m : Matrix (Fin n) (Fin n) ℂ => m i j) := by
  fun_prop

theorem contDiff_qdist : ContDiff ℝ ∞ (qdist (n := n)) := by
  unfold qdist
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  have he : ContDiff ℝ ∞ (fun m : Matrix (Fin n) (Fin n) ℂ => m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j) :=
    (contDiff_entry i j).sub contDiff_const
  exact ((Complex.reCLM.contDiff.comp he).pow 2).add ((Complex.imCLM.contDiff.comp he).pow 2)

theorem entry_sq_le_qdist (m : Matrix (Fin n) (Fin n) ℂ) (i j : Fin n) :
    ‖m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 ≤ qdist m := by
  have e : ‖m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 =
      (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).re ^ 2 + (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j).im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
  rw [e]
  unfold qdist
  calc _ ≤ ∑ j', ((m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').re ^ 2 +
        (m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').im ^ 2) :=
        Finset.single_le_sum (f := fun j' => (m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').re ^ 2 +
          (m i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j').im ^ 2) (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j', ((m i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j').re ^ 2 +
          (m i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j').im ^ 2)) (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity)
          (Finset.mem_univ i)

theorem qdist_one : qdist (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by simp [qdist]

def bumpQ (r : ℝ) (m : Matrix (Fin n) (Fin n) ℂ) : ℝ := Real.smoothTransition (1 - qdist m / r ^ 2)

theorem bumpQ_contDiff (r : ℝ) : ContDiff ℝ ∞ (bumpQ (n := n) r) :=
  Real.smoothTransition.contDiff.comp (contDiff_const.sub (contDiff_qdist.div_const _))

theorem bumpQ_nonneg (r : ℝ) (m : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ bumpQ r m := Real.smoothTransition.nonneg _

theorem bumpQ_pos_one {r : ℝ} : 0 < bumpQ (n := n) r 1 := by
  unfold bumpQ
  apply Real.smoothTransition.pos_of_pos
  rw [qdist_one]
  simp

theorem bumpQ_eq_zero {r : ℝ} (hr : 0 < r) {m : Matrix (Fin n) (Fin n) ℂ} (hm : r ≤ ‖m - 1‖) : bumpQ r m = 0 := by
  unfold bumpQ
  apply Real.smoothTransition.zero_of_nonpos
  have : r ^ 2 ≤ qdist m := by

    by_contra hlt
    push Not at hlt
    have hall : ∀ i j, ‖(m - 1) i j‖ < r := fun i j => by
      have h := entry_sq_le_qdist m i j
      rw [Matrix.sub_apply]
      nlinarith [norm_nonneg (m i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j)]
    exact absurd (Matrix.norm_lt_iff hr |>.2 hall) (not_lt.2 hm)
  rw [sub_nonpos, le_div_iff₀ (by positivity)]
  linarith

theorem bumpQ_support {r : ℝ} (hr : 0 < r) {m : Matrix (Fin n) (Fin n) ℂ} (hm : bumpQ r m ≠ 0) : ‖m - 1‖ < r := by
  by_contra h
  push_neg at h
  exact hm (bumpQ_eq_zero hr h)

theorem bumpQ_compact {r : ℝ} (hr : 0 < r) : HasCompactSupport (bumpQ (n := n) r) := by
  refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) fun m hm => ?_
  rw [Metric.mem_closedBall, dist_eq_norm, not_le] at hm
  exact bumpQ_eq_zero hr hm.le

theorem approx_id (ε : Fin n → Bool) (f : PI.UpqRep.UJ ε → ℂ) (hf : Continuous f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Φ : Matrix (Fin n) (Fin n) ℂ → ℂ, ContDiff ℝ ∞ Φ ∧ HasCompactSupport Φ ∧
      ‖(∫ h, Φ (PI.UpqRep.umat h) * f h ∂(PI.UpqRep.muG ε)) - f 1‖ ≤ δ := by
  have hemb : Topology.IsClosedEmbedding (PI.UpqRep.umat (ε := ε)) := (PI.UpqRep.isClosedEmbeddingMatrix n ε).1
  have hcont1 : ∀ᶠ h in 𝓝 (1 : PI.UpqRep.UJ ε), ‖f h - f 1‖ < δ := by
    have hev := (hf.tendsto 1).eventually (Metric.ball_mem_nhds (f 1) hδ)
    filter_upwards [hev] with h hh
    rwa [dist_eq_norm] at hh
  rw [hemb.isInducing.nhds_eq_comap, Filter.eventually_comap] at hcont1
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff_ball.1 hcont1
  have hu1 : PI.UpqRep.umat (1 : PI.UpqRep.UJ ε) = 1 := rfl
  set b : PI.UpqRep.UJ ε → ℝ := fun h => bumpQ r (PI.UpqRep.umat h) with hb_def
  have hb_cont : Continuous b := (bumpQ_contDiff r).continuous.comp hemb.continuous
  have hb_cs : HasCompactSupport b := (bumpQ_compact hr).comp_isClosedEmbedding hemb
  have hb_nn : 0 ≤ b := fun h => bumpQ_nonneg r _
  have hb1 : b 1 ≠ 0 := by
    show bumpQ r (PI.UpqRep.umat (1 : PI.UpqRep.UJ ε)) ≠ 0
    rw [hu1]
    exact bumpQ_pos_one.ne'
  have hI : 0 < ∫ h, b h ∂(PI.UpqRep.muG ε) :=
    hb_cont.integral_pos_of_hasCompactSupport_nonneg_nonzero hb_cs hb_nn hb1
  set I := ∫ h, b h ∂(PI.UpqRep.muG ε) with hI_def
  have hint_b : Integrable b (PI.UpqRep.muG ε) := hb_cont.integrable_of_hasCompactSupport hb_cs
  refine ⟨fun m => ((bumpQ r m / I : ℝ) : ℂ), ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((bumpQ_contDiff r).div_const I)
  · exact (bumpQ_compact hr).comp_left (g := fun x : ℝ => ((x / I : ℝ) : ℂ)) (by simp)
  · show ‖(∫ h, ((b h / I : ℝ) : ℂ) * f h ∂(PI.UpqRep.muG ε)) - f 1‖ ≤ δ
    have hsum1 : ∫ h, ((b h / I : ℝ) : ℂ) ∂(PI.UpqRep.muG ε) = 1 := by
      rw [integral_complex_ofReal, integral_div, div_self hI.ne']
      simp
    have hi1 : Integrable (fun h => ((b h / I : ℝ) : ℂ) * f h) (PI.UpqRep.muG ε) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact (Complex.continuous_ofReal.comp (hb_cont.div_const I)).mul hf
      · exact (hb_cs.comp_left (g := fun x : ℝ => ((x / I : ℝ) : ℂ)) (by simp)).mul_right
    have hi2 : Integrable (fun h => ((b h / I : ℝ) : ℂ) * f 1) (PI.UpqRep.muG ε) :=
      (hint_b.div_const I).ofReal.mul_const _
    have key : (∫ h, ((b h / I : ℝ) : ℂ) * f h ∂(PI.UpqRep.muG ε)) - f 1
        = ∫ h, ((b h / I : ℝ) : ℂ) * (f h - f 1) ∂(PI.UpqRep.muG ε) := by
      simp_rw [mul_sub]
      rw [integral_sub hi1 hi2, integral_mul_const, hsum1, one_mul]
    rw [key]
    calc ‖∫ h, ((b h / I : ℝ) : ℂ) * (f h - f 1) ∂(PI.UpqRep.muG ε)‖
        ≤ ∫ h, (b h / I) * δ ∂(PI.UpqRep.muG ε) := by
          apply norm_integral_le_of_norm_le ((hint_b.div_const I).mul_const δ)
          refine Filter.Eventually.of_forall fun h => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg (hb_nn h) hI.le)]
          by_cases hz : b h = 0
          · simp [hz]
          · apply mul_le_mul_of_nonneg_left _ (div_nonneg (hb_nn h) hI.le)
            have hlt := bumpQ_support hr hz
            refine (hball _ ?_ h rfl).le
            rw [Metric.mem_ball, dist_eq_norm, hu1]
            exact hlt
      _ = δ := by rw [integral_mul_const, integral_div, div_self hI.ne', one_mul]

end Formalism.IndefR.Eqv.KerDiag

end
