import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutSEJSliceCut

open MeasureTheory Filter Topology Set

noncomputable section

namespace Formalism.FourierDecayAlt.P.CutSE

theorem sob1 {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {a b : ℝ} (hab : a < b) {φ φ' : ℝ → E}
    (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖φ x‖ ^ 2 ≤ 2 / (b - a) * (∫ y in Icc a b, ‖φ y‖ ^ 2) + 8 * (b - a) * ∫ y in Icc a b, ‖φ' y‖ ^ 2 := by
  have hL : 0 < b - a := sub_pos.2 hab
  have hφc : ContinuousOn φ (Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hi1 : IntegrableOn (fun y => ‖φ y‖ ^ 2) (Icc a b) :=
    (hφc.norm.pow 2).integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun y => ‖φ' y‖ ^ 2) (Icc a b) :=
    (hc.norm.pow 2).integrableOn_compact isCompact_Icc
  have hi3 : IntegrableOn (fun y => ‖φ' y‖) (Icc a b) := hc.norm.integrableOn_compact isCompact_Icc
  have hconst : ∀ c : ℝ, IntegrableOn (fun _ : ℝ => c) (Icc a b) := fun c =>
    continuousOn_const.integrableOn_compact isCompact_Icc
  have hvol : volume.real (Icc a b) = b - a := by
    rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal hL.le]
  set P := ∫ y in Icc a b, ‖φ' y‖ with hP
  set Q := ∫ y in Icc a b, ‖φ' y‖ ^ 2 with hQ
  set A := ∫ y in Icc a b, ‖φ y‖ ^ 2 with hA
  have hQ0 : 0 ≤ Q := setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
  have hdiff : ∀ y ∈ Icc a b, ‖φ x - φ y‖ ≤ P := by
    intro y hy
    have hsub : uIcc y x ⊆ Icc a b := uIcc_subset_Icc hy hx
    have hftc : ∫ t in y..x, φ' t = φ x - φ y :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t ht => hd t (hsub ht))
        ((hc.mono hsub).intervalIntegrable)
    rw [← hftc]
    refine intervalIntegral.norm_integral_le_integral_norm_uIoc.trans ?_
    exact setIntegral_mono_set hi3 (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall (uIoc_subset_uIcc.trans hsub))
  have hpt : ∀ y ∈ Icc a b, ‖φ x‖ ^ 2 ≤ 2 * ‖φ y‖ ^ 2 + 2 * P ^ 2 := by
    intro y hy
    have h1 : ‖φ x‖ ≤ ‖φ y‖ + P := by
      have := norm_sub_norm_le (φ x) (φ y)
      linarith [hdiff y hy]
    have h0 : 0 ≤ ‖φ x‖ := norm_nonneg _
    nlinarith [mul_self_le_mul_self h0 h1, sq_nonneg (‖φ y‖ - P)]
  have hmono : ∫ _ in Icc a b, ‖φ x‖ ^ 2 ≤ ∫ y in Icc a b, (2 * ‖φ y‖ ^ 2 + 2 * P ^ 2) :=
    setIntegral_mono_on (hconst _) ((hi1.const_mul 2).add (hconst _)) measurableSet_Icc hpt
  rw [setIntegral_const, hvol, smul_eq_mul, integral_add (hi1.const_mul 2) (hconst _),
    integral_const_mul, setIntegral_const, hvol, smul_eq_mul] at hmono
  have hPQ : P ^ 2 ≤ (b - a) * Q := by
    have hnn : 0 ≤ ∫ y in Icc a b, (‖φ' y‖ - P / (b - a)) ^ 2 :=
      setIntegral_nonneg measurableSet_Icc fun y _ => sq_nonneg _
    have hexp : ∫ y in Icc a b, (‖φ' y‖ - P / (b - a)) ^ 2 =
        Q - 2 * (P / (b - a)) * P + (b - a) * (P / (b - a)) ^ 2 := by
      have hfun : (fun y => (‖φ' y‖ - P / (b - a)) ^ 2) =
          fun y => ‖φ' y‖ ^ 2 - 2 * (P / (b - a)) * ‖φ' y‖ + (P / (b - a)) ^ 2 := by
        funext y
        ring
      rw [hfun, integral_add (f := fun y => ‖φ' y‖ ^ 2 - 2 * (P / (b - a)) * ‖φ' y‖)
        (g := fun _ => (P / (b - a)) ^ 2) (by exact hi2.sub (hi3.const_mul (2 * (P / (b - a))))) (hconst _),
        integral_sub (f := fun y => ‖φ' y‖ ^ 2) (g := fun y => 2 * (P / (b - a)) * ‖φ' y‖) hi2
          (hi3.const_mul (2 * (P / (b - a)))), integral_const_mul, setIntegral_const, hvol, smul_eq_mul]
    rw [hexp] at hnn
    have hsimp : Q - 2 * (P / (b - a)) * P + (b - a) * (P / (b - a)) ^ 2 = Q - P ^ 2 / (b - a) := by
      field_simp
      ring
    rw [hsimp, sub_nonneg, div_le_iff₀ hL] at hnn
    linarith
  have key : (b - a) * ‖φ x‖ ^ 2 ≤ 2 * A + (b - a) * (2 * ((b - a) * Q)) := by
    nlinarith [mul_le_mul_of_nonneg_left hPQ (by positivity : (0 : ℝ) ≤ 2 * (b - a))]
  have hx2 : ‖φ x‖ ^ 2 ≤ (2 * A + (b - a) * (2 * ((b - a) * Q))) / (b - a) := by
    rw [le_div_iff₀ hL]
    linarith
  have he : (2 * A + (b - a) * (2 * ((b - a) * Q))) / (b - a) = 2 / (b - a) * A + 2 * (b - a) * Q := by
    field_simp
  rw [he] at hx2
  nlinarith [mul_nonneg hL.le hQ0]

theorem sob1' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} (hab : a < b) {φ φ' : ℝ → E}
    (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ‖φ x‖ ^ 2 ≤ 2 / (b - a) * (∫ y in Icc a b, ‖φ y‖ ^ 2) + 8 * (b - a) * ∫ y in Icc a b, ‖φ' y‖ ^ 2 := by
  let ι : E →L[ℝ] UniformSpace.Completion E := UniformSpace.Completion.toComplL
  have hd' : ∀ t ∈ Icc a b, HasDerivAt (fun s => ι (φ s)) (ι (φ' t)) t := fun t ht =>
    ι.hasFDerivAt.comp_hasDerivAt t (hd t ht)
  have hc' : ContinuousOn (fun s => ι (φ' s)) (Icc a b) := ι.continuous.comp_continuousOn hc
  have h := sob1 hab hd' hc' hx
  simpa [ι, UniformSpace.Completion.norm_coe] using h

theorem path_hasDerivAt_im (x v : ℝ) :
    HasDerivAt (fun w : ℝ => (x : ℂ) + (w : ℂ) * Complex.I) Complex.I v := by
  simpa using (((hasDerivAt_id v).ofReal_comp).mul_const Complex.I).const_add (x : ℂ)

theorem path_hasDerivAt_re (u v : ℝ) :
    HasDerivAt (fun w : ℝ => (w : ℂ) + (v : ℂ) * Complex.I) 1 u := by
  simpa using ((hasDerivAt_id u).ofReal_comp).add_const ((v : ℂ) * Complex.I)

theorem path_cont_re (v : ℝ) : Continuous (fun w : ℝ => (w : ℂ) + (v : ℂ) * Complex.I) := by
  fun_prop

theorem path_cont_im (x : ℝ) : Continuous (fun w : ℝ => (x : ℂ) + (w : ℂ) * Complex.I) := by
  fun_prop

private theorem sq_norm_le_of_hasDerivAt_on_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ℝ} (hab : a < b)
    {φ φ' : ℝ → E} (hd : ∀ x ∈ Icc a b, HasDerivAt φ (φ' x) x) (hc : ContinuousOn φ' (Icc a b))
    {x : ℝ} (hx : x ∈ Icc a b) :
    ENNReal.ofReal (‖φ x‖ ^ 2) ≤
      ENNReal.ofReal (2 / (b - a)) * (∫⁻ y in Icc a b, ENNReal.ofReal (‖φ y‖ ^ 2)) +
        ENNReal.ofReal (8 * (b - a)) * ∫⁻ y in Icc a b, ENNReal.ofReal (‖φ' y‖ ^ 2) := by
  have hL : 0 < b - a := sub_pos.2 hab
  have hφc : ContinuousOn φ (Icc a b) := fun t ht => (hd t ht).continuousAt.continuousWithinAt
  have hi1 : IntegrableOn (fun y => ‖φ y‖ ^ 2) (Icc a b) :=
    (hφc.norm.pow 2).integrableOn_compact isCompact_Icc
  have hi2 : IntegrableOn (fun y => ‖φ' y‖ ^ 2) (Icc a b) :=
    (hc.norm.pow 2).integrableOn_compact isCompact_Icc
  have h1 : 0 ≤ ∫ y in Icc a b, ‖φ y‖ ^ 2 := setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  have h2 : 0 ≤ ∫ y in Icc a b, ‖φ' y‖ ^ 2 := setIntegral_nonneg measurableSet_Icc fun _ _ => sq_nonneg _
  refine (ENNReal.ofReal_le_ofReal (sob1' hab hd hc hx)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_add (mul_nonneg (by positivity) h1) (mul_nonneg (by positivity) h2),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 / (b - a) by positivity),
    ENNReal.ofReal_mul (show (0 : ℝ) ≤ 8 * (b - a) by positivity),
    ofReal_integral_eq_lintegral_ofReal hi1 (Filter.Eventually.of_forall fun _ => sq_nonneg _),
    ofReal_integral_eq_lintegral_ofReal hi2 (Filter.Eventually.of_forall fun _ => sq_nonneg _)]

theorem spectral_sobolev_second_order : JSSob2 := by
  intro t0 δ hδ
  refine ⟨(2 / δ + 8 * δ) ^ 2, ?_⟩
  intro E _ _ f fx fy fxy hf hfy hfxc hfxyc t ht
  obtain ⟨x, y, rfl⟩ : ∃ x y : ℝ, t = (x : ℂ) + (y : ℂ) * Complex.I :=
    ⟨t.re, t.im, (Complex.re_add_im t).symm⟩
  set D := Metric.closedBall t0 (2 * δ) with hD
  have hh0 : 0 < δ / 2 := by positivity
  have hfC : ContinuousOn f D := fun p hp => (hf p hp).continuousAt.continuousWithinAt
  have hfyC : ContinuousOn fy D := fun p hp => by
    obtain ⟨_, H⟩ := hfy p hp
    exact H.continuousAt.continuousWithinAt
  set g : ℂ → ℝ := fun p => ‖f p‖ ^ 2 + ‖fx p‖ ^ 2 + ‖fy p‖ ^ 2 + ‖fxy p‖ ^ 2 with hg
  have hg0 : ∀ p, 0 ≤ g p := fun p => by simp only [hg]; positivity
  have hgC : ContinuousOn g D :=
    (((hfC.norm.pow 2).add (hfxc.norm.pow 2)).add (hfyC.norm.pow 2)).add (hfxyc.norm.pow 2)
  have hin : ∀ u ∈ Icc (x - δ / 2) (x + δ / 2), ∀ w ∈ Icc (y - δ / 2) (y + δ / 2),
      (u : ℂ) + (w : ℂ) * Complex.I ∈ D := by
    intro u hu w hw
    rw [hD, Metric.mem_closedBall]
    have hz : (u : ℂ) + (w : ℂ) * Complex.I - ((x : ℂ) + (y : ℂ) * Complex.I) =
        ((u - x : ℝ) : ℂ) + ((w - y : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hu' : |u - x| ≤ δ / 2 := abs_le.2 ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have hw' : |w - y| ≤ δ / 2 := abs_le.2 ⟨by linarith [hw.1], by linarith [hw.2]⟩
    have h1 : dist ((u : ℂ) + (w : ℂ) * Complex.I) ((x : ℂ) + (y : ℂ) * Complex.I) ≤ δ := by
      rw [dist_eq_norm, hz]
      refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
      simp only [Complex.add_re, Complex.ofReal_re, Complex.re_ofReal_mul, Complex.I_re, mul_zero,
        add_zero, Complex.add_im, Complex.ofReal_im, Complex.im_ofReal_mul, Complex.I_im, mul_one,
        zero_add]
      linarith
    have h2 : dist ((x : ℂ) + (y : ℂ) * Complex.I) t0 < δ := ht
    linarith [dist_triangle ((u : ℂ) + (w : ℂ) * Complex.I) ((x : ℂ) + (y : ℂ) * Complex.I) t0]
  have hxA : x ∈ Icc (x - δ / 2) (x + δ / 2) := ⟨by linarith, by linarith⟩
  have hyB : y ∈ Icc (y - δ / 2) (y + δ / 2) := ⟨by linarith, by linarith⟩
  have hab : ∀ c : ℝ, c - δ / 2 < c + δ / 2 := fun c => by linarith
  have hL : ∀ c : ℝ, c + δ / 2 - (c - δ / 2) = δ := fun c => by ring
  have dIm : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D →
      HasDerivAt (fun s : ℝ => f ((u : ℂ) + (s : ℂ) * Complex.I)) (fy ((u : ℂ) + (w : ℂ) * Complex.I)) w := by
    intro u w hp
    have := (hf _ hp).comp_hasDerivAt w (path_hasDerivAt_im u w)
    simpa [Function.comp_def] using this
  have dRe : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D →
      HasDerivAt (fun s : ℝ => f ((s : ℂ) + (w : ℂ) * Complex.I)) (fx ((u : ℂ) + (w : ℂ) * Complex.I)) u := by
    intro u w hp
    have := (hf _ hp).comp_hasDerivAt u (path_hasDerivAt_re u w)
    simpa [Function.comp_def] using this
  have dReY : ∀ u w : ℝ, (u : ℂ) + (w : ℂ) * Complex.I ∈ D →
      HasDerivAt (fun s : ℝ => fy ((s : ℂ) + (w : ℂ) * Complex.I)) (fxy ((u : ℂ) + (w : ℂ) * Complex.I)) u := by
    intro u w hp
    obtain ⟨_, H⟩ := hfy _ hp
    have := H.comp_hasDerivAt u (path_hasDerivAt_re u w)
    simpa [Function.comp_def] using this
  have hCeq : ENNReal.ofReal (2 / δ) + ENNReal.ofReal (8 * δ) = ENNReal.ofReal (2 / δ + 8 * δ) :=
    (ENNReal.ofReal_add (by positivity) (by positivity)).symm
  have hC : ENNReal.ofReal (2 / δ + 8 * δ) ≠ ⊤ := ENNReal.ofReal_ne_top
  have step2f : ∀ w ∈ Icc (y - δ / 2) (y + δ / 2),
      ENNReal.ofReal (‖f ((x : ℂ) + (w : ℂ) * Complex.I)‖ ^ 2) ≤
        ENNReal.ofReal (2 / δ + 8 * δ) *
          ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I)) := by
    intro w hw
    have hs := sq_norm_le_of_hasDerivAt_on_Icc (hab x) (φ := fun s : ℝ => f ((s : ℂ) + (w : ℂ) * Complex.I))
      (φ' := fun s : ℝ => fx ((s : ℂ) + (w : ℂ) * Complex.I))
      (fun u hu => dRe u w (hin u hu w hw))
      (hfxc.comp (path_cont_re w).continuousOn fun u hu => hin u hu w hw) hxA
    rw [hL x] at hs
    refine hs.trans ?_
    rw [← hCeq, add_mul]
    refine add_le_add (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
      (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
    · simp only [hg]
      nlinarith [sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]
    · simp only [hg]
      nlinarith [sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]
  have step2fy : ∀ w ∈ Icc (y - δ / 2) (y + δ / 2),
      ENNReal.ofReal (‖fy ((x : ℂ) + (w : ℂ) * Complex.I)‖ ^ 2) ≤
        ENNReal.ofReal (2 / δ + 8 * δ) *
          ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I)) := by
    intro w hw
    have hs := sq_norm_le_of_hasDerivAt_on_Icc (hab x) (φ := fun s : ℝ => fy ((s : ℂ) + (w : ℂ) * Complex.I))
      (φ' := fun s : ℝ => fxy ((s : ℂ) + (w : ℂ) * Complex.I))
      (fun u hu => dReY u w (hin u hu w hw))
      (hfxyc.comp (path_cont_re w).continuousOn fun u hu => hin u hu w hw) hxA
    rw [hL x] at hs
    refine hs.trans ?_
    rw [← hCeq, add_mul]
    refine add_le_add (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
      (mul_le_mul' le_rfl (lintegral_mono fun u => ENNReal.ofReal_le_ofReal ?_))
    · simp only [hg]
      nlinarith [sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fxy ((u : ℂ) + (w : ℂ) * Complex.I)‖]
    · simp only [hg]
      nlinarith [sq_nonneg ‖f ((u : ℂ) + (w : ℂ) * Complex.I)‖, sq_nonneg ‖fy ((u : ℂ) + (w : ℂ) * Complex.I)‖,
        sq_nonneg ‖fx ((u : ℂ) + (w : ℂ) * Complex.I)‖]
  have step1 := sq_norm_le_of_hasDerivAt_on_Icc (hab y) (φ := fun s : ℝ => f ((x : ℂ) + (s : ℂ) * Complex.I))
    (φ' := fun s : ℝ => fy ((x : ℂ) + (s : ℂ) * Complex.I))
    (fun w hw => dIm x w (hin x hxA w hw))
    (hfyC.comp (path_cont_im x).continuousOn fun w hw => hin x hxA w hw) hyB
  rw [hL y] at step1
  have hJ1 := lintegral_mono_ae (μ := volume.restrict (Icc (y - δ / 2) (y + δ / 2)))
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall step2f))
  have hJ2 := lintegral_mono_ae (μ := volume.restrict (Icc (y - δ / 2) (y + δ / 2)))
    ((ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall step2fy))
  rw [lintegral_const_mul' _ _ hC] at hJ1 hJ2
  set J := ∫⁻ w in Icc (y - δ / 2) (y + δ / 2),
    ∫⁻ u in Icc (x - δ / 2) (x + δ / 2), ENNReal.ofReal (g ((u : ℂ) + (w : ℂ) * Complex.I)) with hJ
  have hmain : ENNReal.ofReal (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤
      ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) * J := by
    refine step1.trans ?_
    calc _ ≤ ENNReal.ofReal (2 / δ) * (ENNReal.ofReal (2 / δ + 8 * δ) * J) +
          ENNReal.ofReal (8 * δ) * (ENNReal.ofReal (2 / δ + 8 * δ) * J) :=
          add_le_add (mul_le_mul' le_rfl hJ1) (mul_le_mul' le_rfl hJ2)
      _ = ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) * J := by
          rw [← add_mul, hCeq, mul_assoc]
  have hJD : J ≤ ∫⁻ z in D, ENNReal.ofReal (g z) := by
    have hpc : Continuous fun p : ℝ × ℝ => (p.1 : ℂ) + (p.2 : ℂ) * Complex.I := by fun_prop
    have hGc : ContinuousOn (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
        (Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2)) :=
      ENNReal.continuous_ofReal.comp_continuousOn
        (hgC.comp hpc.continuousOn fun p hp => hin p.1 hp.1 p.2 hp.2)
    have hmeas : AEMeasurable (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
        ((volume.restrict (Icc (x - δ / 2) (x + δ / 2))).prod (volume.restrict (Icc (y - δ / 2) (y + δ / 2)))) := by
      rw [Measure.prod_restrict]
      exact hGc.aemeasurable (measurableSet_Icc.prod measurableSet_Icc)
    have hfub : J = ∫⁻ p in Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2),
        ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)) := by
      rw [Measure.volume_eq_prod, ← Measure.prod_restrict, lintegral_prod_symm _ hmeas]
    have hmp := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
      Complex.measurableEquivRealProd.measurableEmbedding
      (fun p : ℝ × ℝ => ENNReal.ofReal (g ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)))
      (Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2))
    simp only [Complex.measurableEquivRealProd_apply, Complex.re_add_im] at hmp
    rw [hfub, ← hmp]
    refine lintegral_mono_set fun z hz => ?_
    have hz' : (z.re, z.im) ∈ Icc (x - δ / 2) (x + δ / 2) ×ˢ Icc (y - δ / 2) (y + δ / 2) := by
      simpa [Complex.measurableEquivRealProd_apply] using hz
    have := hin z.re hz'.1 z.im hz'.2
    rwa [Complex.re_add_im] at this
  have hgi : IntegrableOn g D := hgC.integrableOn_compact (isCompact_closedBall _ _)
  have hG : ∫⁻ z in D, ENNReal.ofReal (g z) = ENNReal.ofReal (∫ z in D, g z) :=
    (ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall fun z => hg0 z)).symm
  have hint_nn : 0 ≤ (2 / δ + 8 * δ) ^ 2 * ∫ z in D, g z :=
    mul_nonneg (sq_nonneg _) (setIntegral_nonneg measurableSet_closedBall fun z _ => hg0 z)
  have hfin : ENNReal.ofReal (‖f ((x : ℂ) + (y : ℂ) * Complex.I)‖ ^ 2) ≤
      ENNReal.ofReal ((2 / δ + 8 * δ) ^ 2 * ∫ z in D, g z) := by
    calc _ ≤ ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) * J := hmain
      _ ≤ ENNReal.ofReal (2 / δ + 8 * δ) * ENNReal.ofReal (2 / δ + 8 * δ) *
          ∫⁻ z in D, ENNReal.ofReal (g z) := mul_le_mul' le_rfl hJD
      _ = _ := by
        rw [hG, ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ 2 / δ + 8 * δ by positivity),
          ← ENNReal.ofReal_mul (show (0 : ℝ) ≤ (2 / δ + 8 * δ) * (2 / δ + 8 * δ) by positivity)]
        congr 1
        ring
  exact (ENNReal.ofReal_le_ofReal_iff hint_nn).1 hfin

end Formalism.FourierDecayAlt.P.CutSE
