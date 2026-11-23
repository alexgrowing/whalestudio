import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshLap
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PshMean
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement

open MeasureTheory Metric Set Filter Topology Real

namespace ReciprocityTheory.AnForm.A.PshLap

noncomputable section

variable {D : ℕ}

def L0 (w : Fin D → ℂ) : ℂ →L[ℝ] (Fin D → ℂ) := (ContinuousLinearMap.id ℝ ℂ).smulRight w

def Pc (w : Fin D → ℂ) : ((Fin D → ℂ) →L[ℝ] ℝ) →L[ℝ] (ℂ →L[ℝ] ℝ) :=
  (ContinuousLinearMap.compL ℝ ℂ (Fin D → ℂ) ℝ).flip (L0 w)

def Gc (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℝ :=
  Pc w (fderiv ℝ φ (z + ζ • w))

def Hc (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ : ℂ) : ℂ →L[ℝ] ℂ →L[ℝ] ℝ :=
  (Pc w).comp ((fderiv ℝ (fderiv ℝ φ) (z + ζ • w)).comp (L0 w))

lemma complexLine_apply (w : Fin D → ℂ) (a : ℂ) : L0 w a = a • w := by simp [L0]

lemma Pc_apply (w : Fin D → ℂ) (T : (Fin D → ℂ) →L[ℝ] ℝ) (a : ℂ) : Pc w T a = T (a • w) := by
  simp [Pc, L0]

lemma Hc_apply (φ : (Fin D → ℂ) → ℝ) (z w : Fin D → ℂ) (ζ a b : ℂ) :
    Hc φ z w ζ a b = fderiv ℝ (fderiv ℝ φ) (z + ζ • w) (a • w) (b • w) := by
  simp [Hc, Pc, L0]

lemma hasFDerivAt_line (z w : Fin D → ℂ) (ζ : ℂ) :
    HasFDerivAt (fun ζ : ℂ => z + ζ • w) (L0 w) ζ :=
  ((hasFDerivAt_id ζ).smul_const w).const_add z

variable {U : Set (Fin D → ℂ)} {φ : (Fin D → ℂ) → ℝ}

lemma line_hasFDerivAt_g (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) {ζ : ℂ}
    (hζ : z + ζ • w ∈ U) : HasFDerivAt (fun ζ : ℂ => φ (z + ζ • w)) (Gc φ z w ζ) ζ := by
  have hd : HasFDerivAt φ (fderiv ℝ φ (z + ζ • w)) (z + ζ • w) :=
    ((hφ.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hζ)).hasFDerivAt
  refine (hd.comp ζ (hasFDerivAt_line z w ζ)).congr_fderiv ?_
  refine ContinuousLinearMap.ext fun a => ?_
  simp [Gc, Pc_apply, complexLine_apply]

lemma line_hasFDerivAt_G (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) {ζ : ℂ}
    (hζ : z + ζ • w ∈ U) : HasFDerivAt (Gc φ z w) (Hc φ z w ζ) ζ := by
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have hd : HasFDerivAt (fderiv ℝ φ) (fderiv ℝ (fderiv ℝ φ) (z + ζ • w)) (z + ζ • w) :=
    ((h2.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hζ)).hasFDerivAt
  exact (Pc w).hasFDerivAt.comp ζ (hd.comp ζ (hasFDerivAt_line z w ζ))

lemma line_contOn_H (hU : IsOpen U) (hφ : ContDiffOn ℝ 2 φ U) (z w : Fin D → ℂ) :
    ContinuousOn (Hc φ z w) {ζ : ℂ | z + ζ • w ∈ U} := by
  have h2 : ContDiffOn ℝ 1 (fderiv ℝ φ) U := hφ.fderiv_of_isOpen hU (by norm_num)
  have h3 : ContinuousOn (fderiv ℝ (fderiv ℝ φ)) U := h2.continuousOn_fderiv_of_isOpen hU le_rfl
  have hl : Continuous (fun ζ : ℂ => z + ζ • w) := by fun_prop
  exact continuousOn_const.clm_comp
    ((h3.comp hl.continuousOn (fun ζ h => h)).clm_comp continuousOn_const)

lemma circ_smul (r θ : ℝ) (w : Fin D → ℂ) :
    circleMap 0 r θ • w = circleMap 0 1 θ • ((r:ℂ) • w) := by
  ext i
  simp [circleMap]
  ring

theorem plurisubharmonicIffLeviNonneg_holds : IsPsh_iff_isLeviPshStatement := by
  intro D U φ hU hφ
  constructor
  · rintro ⟨-, hsub⟩
    refine ⟨hφ, fun z hz w => ?_⟩
    set V := {ζ : ℂ | z + ζ • w ∈ U} with hV
    have hVo : IsOpen V := hU.preimage (by fun_prop)
    have h0 : (0:ℂ) ∈ V := by simpa [V] using hz
    obtain ⟨R, hR0, hR⟩ := Metric.isOpen_iff.mp hVo 0 h0
    have hR' : closedBall (0:ℂ) (R/2) ⊆ V := (closedBall_subset_ball (by linarith)).trans hR
    have key := lap_nonneg_of_sub_mean (V := V) (g := fun ζ => φ (z + ζ • w)) (G := Gc φ z w)
      (H := Hc φ z w) (fun ζ hζ => line_hasFDerivAt_g hU hφ z w hζ)
      (fun ζ hζ => line_hasFDerivAt_G hU hφ z w hζ) (line_contOn_H hU hφ z w)
      (by linarith : (0:ℝ) < R/2) hR' ?_
    · rw [Hc_apply, Hc_apply] at key
      simp only [zero_smul, add_zero, one_smul] at key
      unfold levi
      linarith
    · intro r hr
      have hmem : ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • ((r:ℂ) • w) ∈ U := by
        intro ζ hζ
        rw [smul_smul]
        apply hR'
        rw [mem_closedBall, dist_zero_right, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hr.1]
        nlinarith [norm_nonneg ζ, hr.2]
      have h1 := (hsub z ((r:ℂ) • w) hmem).2
      simp only [zero_smul, add_zero]
      convert h1 using 1
      rw [Real.circleAverage_def, Real.circleAverage_def]
      congr 1
      refine intervalIntegral.integral_congr (fun θ _ => ?_)
      simp only [circ_smul r θ w]
  · rintro ⟨-, hlev⟩
    refine ⟨hφ.continuousOn.upperSemicontinuousOn, fun z w hdisc => ?_⟩
    set V := {ζ : ℂ | z + ζ • w ∈ U} with hV
    have hB : closedBall (0:ℂ) 1 ⊆ V := fun ζ hζ => hdisc ζ (by simpa using hζ)
    have hcont : Continuous fun θ => φ (z + circleMap 0 1 θ • w) :=
      hφ.continuousOn.comp_continuous
        (continuous_const.add ((continuous_circleMap 0 1).smul continuous_const))
        (fun θ => hdisc _ (by simp))
    refine ⟨hcont.intervalIntegrable 0 (2*π), ?_⟩
    have key := le_circleAverage_of_lap_nonneg (V := V) (g := fun ζ => φ (z + ζ • w))
      (G := Gc φ z w) (H := Hc φ z w) (fun ζ hζ => line_hasFDerivAt_g hU hφ z w hζ)
      (fun ζ hζ => line_hasFDerivAt_G hU hφ z w hζ) (line_contOn_H hU hφ z w) zero_le_one hB ?_
    · simpa using key
    · intro x hx θ
      rw [Hc_apply, Hc_apply]
      have := hlev _ (hB hx) (circleMap 0 1 θ • w)
      unfold levi at this
      rw [smul_smul, mul_comm Complex.I] at this
      linarith

end

end ReciprocityTheory.AnForm.A.PshLap

namespace ReciprocityTheory.AnForm.A.PshInh

open MeasureTheory Metric Set Filter Topology Real

noncomputable section

lemma ci_of_cont {f : ℂ → ℝ} (hf : Continuous f) : CircleIntegrable f 0 1 :=
  (hf.comp (continuous_circleMap 0 1)).intervalIntegrable _ _

lemma avg_affine (a b : ℂ) : Real.circleAverage (fun ζ : ℂ => a + ζ * b) 0 1 = a := by
  have h : DiffContOnCl ℂ (fun ζ : ℂ => a + ζ * b) (ball (0:ℂ) |(1:ℝ)|) :=
    (by fun_prop : Differentiable ℂ (fun ζ : ℂ => a + ζ * b)).diffContOnCl
  simpa using h.circleAverage

lemma avg_re_affine (a b c : ℂ) :
    Real.circleAverage (fun ζ : ℂ => (c * (a + ζ * b)).re) 0 1 = (c * a).re := by
  have hi : CircleIntegrable (fun ζ : ℂ => a + ζ * b) 0 1 :=
    ((by fun_prop : Continuous (fun ζ : ℂ => a + ζ * b)).comp
      (continuous_circleMap 0 1)).intervalIntegrable _ _
  let L : ℂ →L[ℝ] ℝ := Complex.reCLM.comp ((ContinuousLinearMap.mul ℂ ℂ c).restrictScalars ℝ)
  have h := L.circleAverage_comp_comm hi
  rw [avg_affine] at h
  simpa [L, Function.comp_def] using h

lemma le_avg_norm (a b : ℂ) : ‖a‖ ≤ Real.circleAverage (fun ζ : ℂ => ‖a + ζ * b‖) 0 1 := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [norm_zero]
    exact Real.circleAverage_nonneg_of_nonneg fun _ _ => norm_nonneg _
  have h1 : ‖a‖ ^ 2 = Real.circleAverage
      (fun ζ : ℂ => ((starRingEnd ℂ) a * (a + ζ * b)).re) 0 1 := by
    rw [avg_re_affine, Complex.conj_mul']
    norm_cast
  have h2 : Real.circleAverage (fun ζ : ℂ => ((starRingEnd ℂ) a * (a + ζ * b)).re) 0 1 ≤
      Real.circleAverage (fun ζ : ℂ => ‖a‖ * ‖a + ζ * b‖) 0 1 := by
    refine Real.circleAverage_mono (ci_of_cont (by fun_prop)) (ci_of_cont (by fun_prop))
      fun x _ => (Complex.re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj]
  have h3 : Real.circleAverage (fun ζ : ℂ => ‖a‖ * ‖a + ζ * b‖) 0 1 =
      ‖a‖ * Real.circleAverage (fun ζ : ℂ => ‖a + ζ * b‖) 0 1 := by
    simpa [smul_eq_mul] using
      Real.circleAverage_fun_smul (a := ‖a‖) (f := fun ζ : ℂ => ‖a + ζ * b‖) (c := 0) (R := 1)
  have hpos : 0 < ‖a‖ := norm_pos_iff.2 ha
  refine le_of_mul_le_mul_left ?_ hpos
  nlinarith

lemma le_avg_sq (a b : ℂ) : ‖a‖ ^ 2 ≤ Real.circleAverage (fun ζ : ℂ => ‖a + ζ * b‖ ^ 2) 0 1 := by
  have key : ∀ x : ℂ, (2 * (starRingEnd ℂ) a * x).re - ‖a‖ ^ 2 ≤ ‖x‖ ^ 2 := by
    intro x
    have := sq_nonneg (x.re - a.re)
    have := sq_nonneg (x.im - a.im)
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    nlinarith
  have hE : Real.circleAverage (fun ζ : ℂ => (2 * (starRingEnd ℂ) a * (a + ζ * b)).re - ‖a‖ ^ 2)
      0 1 = ‖a‖ ^ 2 := by
    rw [Real.circleAverage_fun_sub (ci_of_cont (by fun_prop)) (ci_of_cont (by fun_prop)),
      avg_re_affine, Real.circleAverage_const]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.re_ofNat, Complex.im_ofNat]
    ring
  rw [← hE]
  exact Real.circleAverage_mono (ci_of_cont (by fun_prop)) (ci_of_cont (by fun_prop))
    fun x _ => key _

lemma ii_sup' {ι : Type} [Fintype ι] [Nonempty ι] (f : ι → ℝ → ℝ) {a b : ℝ}
    (hf : ∀ j, IntervalIntegrable (f j) volume a b) :
    IntervalIntegrable (fun θ => Finset.univ.sup' Finset.univ_nonempty (fun j => f j θ))
      volume a b := by
  have e : (fun θ => Finset.univ.sup' Finset.univ_nonempty (fun j => f j θ)) =
      Finset.univ.sup' Finset.univ_nonempty f := by
    funext θ; rw [Finset.sup'_apply]
  rw [e]
  refine Finset.sup'_induction _ _ (p := fun g => IntervalIntegrable g volume a b) ?_
    (fun j _ => hf j)
  intro g hg h hh
  exact ⟨hg.1.sup hh.1, hg.2.sup hh.2⟩

end

end ReciprocityTheory.AnForm.A.PshInh

namespace ReciprocityTheory.AnForm.A

open MeasureTheory Metric Set Filter Topology Real PshInh

theorem isPsh_iff_isLeviPsh_thm : IsPsh_iff_isLeviPshStatement := PshLap.plurisubharmonicIffLeviNonneg_holds

theorem isPshInhabit_thm : IsPshInhabitStatement := by
  intro D
  have hsq : IsPsh (Set.univ : Set (Fin D → ℂ)) (fun z => ∑ j, ‖z j‖ ^ 2) := by
    refine ⟨(by fun_prop : Continuous (fun z : Fin D → ℂ => ∑ j, ‖z j‖ ^ 2)).continuousOn.upperSemicontinuousOn,
      fun z w _ => ⟨ci_of_cont (by fun_prop), ?_⟩⟩
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [Real.circleAverage_fun_sum (fun j _ => ci_of_cont (by fun_prop))]
    exact Finset.sum_le_sum fun j _ => le_avg_sq (z j) (w j)
  have hnorm : IsPsh (Set.univ : Set (Fin D → ℂ)) (fun z => ‖z‖) := by
    refine ⟨continuous_norm.continuousOn.upperSemicontinuousOn,
      fun z w _ => ⟨ci_of_cont (by fun_prop), ?_⟩⟩
    show ‖z‖ ≤ Real.circleAverage (fun ζ : ℂ => ‖z + ζ • w‖) 0 1
    rcases isEmpty_or_nonempty (Fin D) with hD | hD
    · rw [Subsingleton.elim z 0, norm_zero]
      exact Real.circleAverage_nonneg_of_nonneg fun _ _ => norm_nonneg _
    · obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty
        (fun b => ‖z b‖₊)
      have hzj : ‖z‖ = ‖z j‖ := by rw [Pi.norm_def, hj]; rfl
      rw [hzj]
      refine (le_avg_norm (z j) (w j)).trans (Real.circleAverage_mono (ci_of_cont (by fun_prop))
        (ci_of_cont (by fun_prop)) fun ζ _ => ?_)
      simpa using norm_le_pi_norm (z + ζ • w) j
  have hC : ContDiffOn ℝ 2 (fun z : Fin D → ℂ => ∑ j, ‖z j‖ ^ 2) Set.univ :=
    (ContDiff.sum fun j _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ j)).contDiffOn
  refine ⟨hsq, hnorm, (PshLap.plurisubharmonicIffLeviNonneg_holds D _ _ isOpen_univ hC).1 hsq, ?_⟩
  rintro ⟨-, h2⟩
  have h := (h2 0 (Pi.single 0 1) (fun _ _ => Set.mem_univ _)).2
  rw [Real.circleAverage_const_on_circle (a := (-1:ℝ)) (fun x hx => by
    simp only [mem_sphere_iff_norm, sub_zero, abs_one] at hx
    simp [hx])] at h
  norm_num at h

theorem isPsh_sup_thm : IsPsh_supStatement := by
  intro D ι _ _ U u hU hu
  refine ⟨?_, fun z w hdisc => ?_⟩
  · intro x hx y hy
    have : ∀ j, ∀ᶠ x' in 𝓝[U] x, u j x' < y := fun j =>
      (hu j).1 x hx y (lt_of_le_of_lt (Finset.le_sup' (fun j => u j x) (Finset.mem_univ j)) hy)
    filter_upwards [Filter.eventually_all.2 this] with x' hx'
    exact (Finset.sup'_lt_iff _).2 fun j _ => hx' j
  · have hci : ∀ j, CircleIntegrable (fun ζ : ℂ => u j (z + ζ • w)) 0 1 :=
      fun j => ((hu j).2 z w hdisc).1
    have hcs : CircleIntegrable (fun ζ : ℂ =>
        Finset.univ.sup' Finset.univ_nonempty (fun j => u j (z + ζ • w))) 0 1 :=
      ii_sup' (fun j θ => u j (z + circleMap 0 1 θ • w)) hci
    refine ⟨hcs, ?_⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun j => u j z)
    simp only
    rw [hj]
    refine ((hu j).2 z w hdisc).2.trans (Real.circleAverage_mono (hci j) hcs fun ζ _ => ?_)
    exact Finset.le_sup' (fun j => u j (z + ζ • w)) (Finset.mem_univ j)

theorem isPsh_locallyIntegrable_thm : IsPsh_locallyIntegrableStatement :=
  PshMean.plurisubharmonicLocallyIntegrable_holds

theorem subMeanPolydisc_thm : SubMeanPolydiscStatement := PshMean.subMeanValuePolydisc_holds

theorem mollifierInhabit_thm : MollifierInhabitStatement := PshMol.circleInvariantMollifierExists_holds

end ReciprocityTheory.AnForm.A
