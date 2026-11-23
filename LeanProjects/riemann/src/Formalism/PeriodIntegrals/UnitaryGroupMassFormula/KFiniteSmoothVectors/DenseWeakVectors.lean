import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.KFiniteSmoothVectors.UnitaryModelOfMultiplicityGardingDensity

open MeasureTheory Matrix Topology
open scoped InnerProductSpace ContDiff

noncomputable section

namespace PI.KFinSmoothW

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Dense

variable {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

lemma umat_mem_UJset (h : UJ ε) : umat h ∈ UJset ε := h.2

lemma one_mem_UJset : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ UJset ε := by
  exact (UJ ε).one_mem

lemma cont_orbit {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hτ : IsURepOn (UJset ε) τ) (u : H) :
    Continuous (fun h : UJ ε => τ (umat h) u) := (hτ.2.2 u).comp_continuous (Units.continuous_val.comp continuous_subtype_val) (fun h => h.2)

lemma gv_sub_norm_le [CompleteSpace H] {τ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hτ : IsURepOn (UJset ε) τ)
    (Φr : Matrix (Fin n) (Fin n) ℂ → ℝ) (hΦc : Continuous Φr) (hΦ0 : ∀ x, 0 ≤ Φr x)
    (hint : Integrable (fun h : UJ ε => Φr (umat h)) (muG ε))
    (h1 : ∫ h, Φr (umat h) ∂(muG ε) = 1) (u : H) (δ : ℝ)
    (hsupp : ∀ h : UJ ε, Φr (umat h) ≠ 0 → ‖τ (umat h) u - u‖ ≤ δ) :
    ‖gv ε τ (fun x => (Φr x : ℂ)) u - u‖ ≤ δ := by
  have hc := cont_orbit hτ u
  have hI1 : Integrable (fun h : UJ ε => Φr (umat h) • τ (umat h) u) (muG ε) := by
    refine Integrable.mono' (hint.mul_const ‖u‖) ?_ ?_
    · exact ((hΦc.comp (continuous_coeMatrix ε)).smul hc).aestronglyMeasurable
    · filter_upwards with h
      rw [norm_smul, hτ.2.1 _ (umat_mem_UJset h), Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
  have hI2 : Integrable (fun h : UJ ε => Φr (umat h) • u) (muG ε) := hint.smul_const u
  have hgv : gv ε τ (fun x => (Φr x : ℂ)) u = ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) := by
    unfold gv
    congr 1
  have hu : ∫ h, Φr (umat h) • u ∂(muG ε) = u := by
    rw [integral_smul_const, h1, one_smul]
  have hdiff : ∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε) =
      ∫ h, Φr (umat h) • τ (umat h) u ∂(muG ε) - u := by
    simp_rw [smul_sub]
    rw [integral_sub hI1 hI2, hu]
  rw [hgv, ← hdiff]
  calc ‖∫ h, Φr (umat h) • (τ (umat h) u - u) ∂(muG ε)‖
      ≤ ∫ h, Φr (umat h) * δ ∂(muG ε) := by
        refine norm_integral_le_of_norm_le (hint.mul_const δ) ?_
        filter_upwards with h
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hΦ0 _)]
        by_cases hz : Φr (umat h) = 0
        · simp [hz]
        · exact mul_le_mul_of_nonneg_left (hsupp h hz) (hΦ0 _)
    _ = δ := by rw [integral_mul_const, h1, one_mul]

def qd (x : Matrix (Fin n) (Fin n) ℂ) : ℝ := ∑ i, ∑ j, ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2

lemma qd_contDiff : ContDiff ℝ ∞ (qd (n := n)) := by
  unfold qd
  refine ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
  exact (contDiff_norm_sq ℝ).comp ((contDiff_apply_apply ℝ ℂ i j).sub contDiff_const)

lemma qd_one : qd (1 : Matrix (Fin n) (Fin n) ℂ) = 0 := by
  simp [qd]

lemma qd_eq_trace (x : Matrix (Fin n) (Fin n) ℂ) :
    qd x = (Matrix.trace ((x - 1)ᴴ * (x - 1))).re := by
  simp only [qd, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.re_sum, Matrix.sub_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

lemma qd_conj (a m : Matrix (Fin n) (Fin n) ℂ) (h1 : a * aᴴ = 1) (h2 : aᴴ * a = 1) :
    qd (a * m * aᴴ) = qd m := by
  rw [qd_eq_trace, qd_eq_trace]
  have e : a * m * aᴴ - 1 = a * (m - 1) * aᴴ := by
    rw [mul_sub, sub_mul, mul_one, h1]
  have e2 : (a * (m - 1) * aᴴ)ᴴ * (a * (m - 1) * aᴴ) = a * ((m - 1)ᴴ * (m - 1)) * aᴴ := by
    simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc aᴴ a, h2, Matrix.one_mul]
  rw [e, e2, Matrix.trace_mul_comm, ← Matrix.mul_assoc, h2, Matrix.one_mul]

lemma dist_lt_of_qd_lt {x : Matrix (Fin n) (Fin n) ℂ} {r : ℝ} (hr : 0 < r) (h : qd x < r ^ 2) :
    dist x 1 < r := by
  rw [dist_eq_norm, Matrix.norm_lt_iff hr]
  intro i j
  have hle : ‖(x - 1) i j‖ ^ 2 ≤ qd x := by
    unfold qd
    rw [Matrix.sub_apply]
    calc ‖x i j - (1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2
        ≤ ∑ j', ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2 :=
          Finset.single_le_sum (f := fun j' => ‖x i j' - (1 : Matrix (Fin n) (Fin n) ℂ) i j'‖ ^ 2)
            (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
      _ ≤ ∑ i', ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2 :=
          Finset.single_le_sum
            (f := fun i' => ∑ j', ‖x i' j' - (1 : Matrix (Fin n) (Fin n) ℂ) i' j'‖ ^ 2)
            (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ i)
  nlinarith [norm_nonneg ((x - 1) i j)]

end Dense

theorem dense_weak_vectors : StepDenseW := by
  intro n ε H _ _ _ τ hτ W hW

  let R : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] H) := fun g => (τ g).comp W.subtypeL
  have hR : ContinuousWithinAt R (UJset ε) 1 :=
    continuousWithinAt_clm_apply.2 fun y => hτ.2.2 (y : H) 1 one_mem_UJset
  obtain ⟨r, hr, hr'⟩ := Metric.continuousWithinAt_iff.mp hR (1 / 2) (by norm_num)
  have hτ1 : τ 1 = 1 := hτ.1.1
  have hclose : ∀ g ∈ UJset ε, dist g 1 < r → ∀ w ∈ W, ‖τ g w - w‖ ≤ ‖w‖ / 2 := by
    intro g hg hd w hw
    have h1 := hr' hg hd
    rw [dist_eq_norm] at h1
    have h2 := (R g - R 1).le_opNorm ⟨w, hw⟩
    have h3 : (R g - R 1) ⟨w, hw⟩ = τ g w - w := by
      simp [R, hτ1]
    rw [h3] at h2
    have h4 : ‖(⟨w, hw⟩ : W)‖ = ‖w‖ := rfl
    rw [h4] at h2
    calc ‖τ g w - w‖ ≤ ‖R g - R 1‖ * ‖w‖ := h2
      _ ≤ (1 / 2) * ‖w‖ := mul_le_mul_of_nonneg_right h1.le (norm_nonneg _)
      _ = ‖w‖ / 2 := by ring

  have hr2 : 0 < r ^ 2 := by positivity
  let ψ : ContDiffBump (0 : ℝ) := ⟨r ^ 2 / 2, r ^ 2, half_pos hr2, half_lt_self hr2⟩
  let Φ0 : Matrix (Fin n) (Fin n) ℂ → ℝ := fun x => ψ (qd x)
  have hΦ0c : Continuous Φ0 := ψ.continuous.comp qd_contDiff.continuous
  have hsupp0 : ∀ x, Φ0 x ≠ 0 → dist x 1 < r := by
    intro x hx
    have hb : qd x ∈ Function.support ψ := hx
    rw [ψ.support_eq, Metric.mem_ball, Real.dist_eq, sub_zero] at hb
    exact dist_lt_of_qd_lt hr (lt_of_le_of_lt (le_abs_self _) hb)
  have hcs : HasCompactSupport Φ0 := by
    refine HasCompactSupport.intro (isCompact_closedBall (1 : Matrix (Fin n) (Fin n) ℂ) r) ?_
    intro x hx
    by_contra hne
    exact hx (Metric.mem_closedBall.2 (hsupp0 x hne).le)
  have hcomp : Continuous (fun h : UJ ε => Φ0 (umat h)) := hΦ0c.comp (continuous_coeMatrix ε)
  have hint : Integrable (fun h : UJ ε => Φ0 (umat h)) (muG ε) :=
    hcomp.integrable_of_hasCompactSupport (hcs.comp_isClosedEmbedding (isClosedEmbeddingMatrix n ε).1)
  have hpos : 0 < ∫ h, Φ0 (umat h) ∂(muG ε) := by
    rw [integral_pos_iff_support_of_nonneg (fun h => ψ.nonneg) hint]
    apply IsOpen.measure_pos
    · exact isOpen_ne_fun hcomp continuous_const
    · refine ⟨1, ?_⟩
      show ψ (qd (umat (1 : UJ ε))) ≠ 0
      have h1 : umat (1 : UJ ε) = 1 := rfl
      rw [h1, qd_one, ψ.one_of_mem_closedBall (Metric.mem_closedBall_self ψ.rIn_pos.le)]
      exact one_ne_zero
  set c := ∫ h, Φ0 (umat h) ∂(muG ε) with hc
  refine ⟨fun x => ((Φ0 x / c : ℝ) : ℂ), ?_, ?_, ?_, ?_⟩
  · exact Complex.ofRealCLM.contDiff.comp ((ψ.contDiff.comp qd_contDiff).div_const c)
  · exact hcs.comp_left (g := fun t : ℝ => ((t / c : ℝ) : ℂ)) (by simp)
  · intro a ha m
    have hu1 : a * aᴴ = 1 := by
      have := Unitary.mul_star_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    have hu2 : aᴴ * a = 1 := by
      have := Unitary.star_mul_self_of_mem ha.1
      rwa [Matrix.star_eq_conjTranspose] at this
    simp only [Φ0, qd_conj a m hu1 hu2]
  · intro w hw
    refine gv_sub_norm_le hτ (fun x => Φ0 x / c) (hΦ0c.div_const c)
      (fun x => div_nonneg ψ.nonneg hpos.le) (hint.div_const c)
      (by rw [integral_div, ← hc, div_self hpos.ne']) w (‖w‖ / 2) ?_
    intro h hz
    have hne : Φ0 (umat h) ≠ 0 := by
      intro h0
      apply hz
      show Φ0 (umat h) / c = 0
      rw [h0, zero_div]
    exact hclose _ (umat_mem_UJset h) (hsupp0 _ hne) w hw

end PI.KFinSmoothW
