import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsChart
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IsotropicSublatticeCovolumePositiveStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RiemannLatticeEigenProjectionStatement
import Development.AutomorphicSpectrum.Proofs.MetricProofs.MulVecEqZeroOfPair
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods

variable {n a g : ℕ} {Λ : Type} [AddCommGroup Λ] {L : Flat.LogPeriods n a g Λ}
  {bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ} {A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
  {B : Fin a → Matrix (Fin g) (Fin g) ℤ} {c ρ : ℝ}

theorem exists_ball_det (h : IsChart L bas A T0 B c ρ) :
    ∃ ρ' : ℝ, 0 < ρ' ∧ ρ' ≤ ρ ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0 := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  obtain ⟨ρ₂, K, hρ₂, -, hinv⟩ := GlobalTheory.CompanionTheory.Ar.RiemannLimit.inv n g A
    (h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)) h.A_det
  exact ⟨min ρ₂ ρ, lt_min hρ₂ h.ρ_pos, min_le_right _ _,
    fun z hz => (hinv z (Metric.ball_subset_ball (min_le_left _ _) hz)).1⟩

theorem A_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => A (zs m)) atTop (𝓝 (A 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.A_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem T_tendsto (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) : Tendsto (fun m => T0 (zs m)) atTop (𝓝 (T0 0)) := by
  have h0 : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) 1 := Metric.mem_ball_self one_pos
  exact ((h.T_cont.continuousAt (Metric.isOpen_ball.mem_nhds h0)).tendsto).comp hz

theorem inv_period (h : IsChart L bas A T0 B c ρ) {ρ' : ℝ}
    (hdet : ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ', (A z).det ≠ 0) (w : Fin n → ℂ)
    (hw : w ∈ logCover L.a_le) (hz : expCover a w ∈ Metric.ball (0 : Fin n → ℂ) ρ') (x : Λ) :
    ((A (expCover a w))ᵀ)⁻¹ *ᵥ L.P w x =
      cst (uCo bas x) + tauAt L.a_le T0 B w *ᵥ cst (vCo bas x) := by
  rw [h.per w hw x, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ (Ne.isUnit (by rw [det_transpose]; exact hdet _ hz)),
    Matrix.one_mulVec]

theorem tendsto_inv_mulVec (h : IsChart L bas A T0 B c ρ) {zs : ℕ → Fin n → ℂ}
    (hz : Tendsto zs atTop (𝓝 0)) {q : ℕ → Fin g → ℂ} {p : Fin g → ℂ}
    (hq : Tendsto q atTop (𝓝 p)) :
    Tendsto (fun m => ((A (zs m))ᵀ)⁻¹ *ᵥ q m) atTop (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ p)) := by
  have hinv := tendsto_inv_transpose (A_tendsto h hz) h.A_det
  have hy := (((continuous_fst.matrix_mulVec continuous_snd :
    Continuous fun q : Matrix (Fin g) (Fin g) ℂ × (Fin g → ℂ) => q.1 *ᵥ q.2)).tendsto
      (((A 0)ᵀ)⁻¹, p)).comp (hinv.prodMk_nhds hq)
  exact hy.congr fun m => rfl

theorem ker_each (hB : ∀ j, ((B j).map (fun x : ℤ => (x : ℝ))).PosSemidef) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) (j : Fin a) :
    (B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0 := by
  have hR : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℝ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have h0 : v ⬝ᵥ ((∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v) = 0 := by rw [hv]; simp
  rw [hR, Matrix.sum_mulVec, dotProduct_sum] at h0
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ v ⬝ᵥ ((B i).map (fun x : ℤ => (x : ℝ)) *ᵥ v) := fun i _ => by
    simpa using (hB i).dotProduct_mulVec_nonneg v
  have h1 := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 h0 j (Finset.mem_univ j)
  exact ((hB j).dotProduct_mulVec_zero_iff v).1 (by simpa using h1)

theorem lower_at_centre (h : IsChart L bas A T0 B c ρ) (v : Fin g → ℝ)
    (hv : (∑ j, B j).map (fun x : ℤ => (x : ℝ)) *ᵥ v = 0) :
    c * (v ⬝ᵥ v) ≤ v ⬝ᵥ (((T0 0).map Complex.im) *ᵥ v) := by
  have := GlobalTheory.CompanionTheory.ChartBlockLower.im_lower_on_kernel n a g L.a_le (Metric.ball 0 ρ) T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball h.ρ_le)) h.B_psd h.c_pos h.im_lower
    0 (Metric.mem_ball_self h.ρ_pos) (fun _ => 0) (fun j hj => (hj rfl).elim) (fun _ _ => rfl) v
    (fun j _ => ker_each h.B_psd v hv j)
  simpa using this

theorem exp_cast (ha : a ≤ n) (w : Fin n → ℂ) (j : Fin a) :
    Complex.exp (w (Fin.castLE ha j)) = expCover a w (Fin.castLE ha j) := by
  have hj : (Fin.castLE ha j).val < a := j.2
  simp only [expCover, if_pos hj]

theorem extend_mem (h : IsChart L bas A T0 B c ρ) (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ)
    (ht : ContinuousAt t 0) (hP : ∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) :
    x ∈ chartW bas B := by
  classical
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have h2pi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := Complex.two_pi_I_ne_zero
  set r : ℕ → ℝ := fun m => ρ'⁻¹ + m with hr
  set tm : ℕ → ℂ := fun m => ((r m / (2 * Real.pi) : ℝ) : ℂ) * Complex.I with htm
  set ws : ℕ → Fin n → ℂ := fun m k => if k.val < a then -(r m : ℂ) else 0 with hws
  have hrpos : ∀ m, 0 < r m := fun m => by
    have : 0 < ρ'⁻¹ := inv_pos.2 hρ'
    have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    simp only [hr]; linarith
  have hexpr : ∀ m, Real.exp (-(r m)) < ρ' := by
    intro m
    have h1 : r m + 1 ≤ Real.exp (r m) := Real.add_one_le_exp _
    have h3 : ρ'⁻¹ ≤ r m := by
      have h2 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
      simp only [hr]; linarith
    rw [Real.exp_neg]
    have h4 : ρ'⁻¹ < Real.exp (r m) := by linarith
    exact inv_lt_of_inv_lt₀ hρ' h4
  have hws_cast : ∀ m (j : Fin a), ws m (Fin.castLE L.a_le j) = -(r m : ℂ) := by
    intro m j
    have hj : (Fin.castLE L.a_le j).val < a := j.2
    simp only [hws, if_pos hj]
  have hws_mem : ∀ m, ws m ∈ logCover L.a_le := by
    intro m
    refine ⟨fun i => ?_, fun k hk => ?_⟩
    · rw [hws_cast]
      simp [hrpos m]
    · have hk' : ¬ k.val < a := not_lt.2 hk
      simp only [hws, if_neg hk']
      simp
  set zs : ℕ → Fin n → ℂ := fun m => expCover a (ws m) with hzs
  have hzs_k : ∀ m k, zs m k = if k.val < a then ((Real.exp (-(r m)) : ℝ) : ℂ) else 0 := by
    intro m k
    simp only [hzs, expCover, hws]
    by_cases hk : k.val < a
    · simp [hk]
    · simp [hk]
  have hzs_ball : ∀ m, zs m ∈ Metric.ball (0 : Fin n → ℂ) ρ' := by
    intro m
    rw [mem_ball_zero_iff, pi_norm_lt_iff hρ']
    intro k
    rw [hzs_k]
    split_ifs
    · rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le]; exact hexpr m
    · simpa using hρ'
  have hrtop : Tendsto r atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hzs_lim : Tendsto zs atTop (𝓝 0) := by
    rw [tendsto_pi_nhds]
    intro k
    simp only [hzs_k]
    by_cases hk : k.val < a
    · simp only [hk, if_true]
      have h1 : Tendsto (fun m => Real.exp (-(r m))) atTop (𝓝 0) :=
        Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hrtop)
      have h2 := (Complex.continuous_ofReal.tendsto 0).comp h1
      simpa only [Function.comp_def, Complex.ofReal_zero, Pi.zero_apply] using h2
    · simp only [hk, if_false]
      exact tendsto_const_nhds
  have hdiv : ∀ m, (-(r m : ℂ)) / (2 * Real.pi * Complex.I) = tm m := by
    intro m
    rw [div_eq_iff h2pi]
    have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp only [htm]
    push_cast
    field_simp
    simp
  have hC : (∑ j, B j).map (fun x : ℤ => (x : ℂ)) = ∑ j, (B j).map (fun x : ℤ => (x : ℂ)) := by
    ext p q
    simp [Matrix.sum_apply]
  have hdec : ∀ m, tauAt L.a_le T0 B (ws m) =
      T0 (zs m) + tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
    intro m
    have hsum : ∑ j, (ws m (Fin.castLE L.a_le j) / (2 * Real.pi * Complex.I)) •
        (B j).map (fun x : ℤ => (x : ℂ)) = tm m • (∑ j, B j).map (fun x : ℤ => (x : ℂ)) := by
      rw [hC, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hws_cast, hdiv]
    simp only [tauAt]
    rw [hsum]
  have him : Tendsto (fun m => (tm m).im) atTop atTop := by
    have h1 : ∀ m, (tm m).im = r m / (2 * Real.pi) := fun m => by
      simp only [htm, Complex.mul_I_im, Complex.ofReal_re]
    simp only [h1]
    exact hrtop.atTop_div_const (by positivity)
  have hYm : ∀ m, ((tauAt L.a_le T0 B (ws m)).map Complex.im -
      c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef := fun m =>
    h.im_lower _ (Metric.ball_subset_ball hρle (hzs_ball m))
      (fun j => ws m (Fin.castLE L.a_le j)) (fun j => exp_cast L.a_le (ws m) j)
  have hq := tendsto_inv_mulVec h hzs_lim (ht.tendsto.comp hzs_lim)
  have hy' : Tendsto (fun m => (fun k => ((uCo bas x k : ℤ) : ℂ)) +
      tauAt L.a_le T0 B (ws m) *ᵥ (fun k => ((vCo bas x k : ℤ) : ℂ))) atTop
      (𝓝 (((A 0)ᵀ)⁻¹ *ᵥ t 0)) := hq.congr fun m => by
    have := inv_period h hdet (ws m) (hws_mem m) (hzs_ball m) x
    rw [hP _ (hws_mem m)] at this
    exact this
  obtain ⟨u, v, hv, -, hev⟩ := GlobalTheory.T.siegel_limit_imag_bound g (∑ j, B j) (T0 0) (fun m => T0 (zs m))
    (fun m => tauAt L.a_le T0 B (ws m)) tm c (fun _ => uCo bas x) (fun _ => vCo bas x) _ h.c_pos
    (T_tendsto h hzs_lim) him hdec hYm (lower_at_centre h) hy'
  obtain ⟨m, hm⟩ := hev.exists
  have hvx : vCo bas x = v := hm.2
  rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, hvx, Matrix.mulVecLin_apply]
  exact hv

theorem limit_mem (h : IsChart L bas A T0 B c ρ) (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ)
    (hws : ∀ k, ws k ∈ logCover L.a_le)
    (hz : Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0))
    (hp : Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p)) :
    ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ := by
  obtain ⟨ρ', hρ', hρle, hdet⟩ := exists_ball_det h
  have hU : (0 : Fin n → ℂ) ∈ Metric.ball (0 : Fin n → ℂ) ρ' := Metric.mem_ball_self hρ'
  have hq := tendsto_inv_mulVec h hz hp
  have key := GlobalTheory.CompanionTheory.PeriodLimit.limit_period n a g L.a_le (Metric.ball 0 ρ') T0 B c
    Metric.isOpen_ball (h.T_cont.mono (Metric.ball_subset_ball (hρle.trans h.ρ_le))) h.B_psd h.c_pos
    (fun z hz => h.im_lower z (Metric.ball_subset_ball hρle hz)) 0 hU (fun _ => 0)
    (fun j hj => (hj rfl).elim) (fun _ _ => rfl) (((A 0)ᵀ)⁻¹ *ᵥ p)
  obtain ⟨u, v, hv, hw⟩ := key (mem_closure_of_tendsto (hz.prodMk_nhds hq) (by
    filter_upwards [hz.eventually (Metric.isOpen_ball.mem_nhds hU)] with k hk
    exact ⟨hk, fun j => ws k (Fin.castLE L.a_le j), uCo bas (x k), vCo bas (x k),
      fun j => exp_cast L.a_le (ws k) j, inv_period h hdet _ (hws k) hk (x k)⟩))
  simp only [zero_div, zero_smul, Finset.sum_const_zero, add_zero] at hw
  have hw' : ((A 0)ᵀ)⁻¹ *ᵥ p = cst u + T0 0 *ᵥ cst v := hw
  refine ⟨⟨mk bas u v, ?_⟩, ?_⟩
  · rw [chartW, LinearMap.mem_ker, LinearMap.comp_apply, vCo_mk, Matrix.mulVecLin_apply,
      Matrix.sum_mulVec]
    exact Finset.sum_eq_zero fun j _ => hv j rfl
  · show p = (A 0)ᵀ *ᵥ (cst (uCo bas (mk bas u v)) + T0 0 *ᵥ cst (vCo bas (mk bas u v)))
    rw [uCo_mk, vCo_mk, ← hw', Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv _ (Ne.isUnit (by rw [det_transpose]; exact h.A_det)),
      Matrix.one_mulVec]

theorem periods_at_centre : ∀ (n a g : ℕ) (Λ : Type) [AddCommGroup Λ] (L : Flat.LogPeriods n a g Λ) (bas : Module.Basis (Fin g ⊕ Fin g) ℤ Λ) (A T0 : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ) (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (c ρ : ℝ), IsChart L bas A T0 B c ρ → (∀ (x : Λ) (t : (Fin n → ℂ) → Fin g → ℂ), ContinuousAt t 0 → (∀ w ∈ logCover L.a_le, L.P w x = t (expCover a w)) → x ∈ chartW bas B) ∧ ∀ (ws : ℕ → Fin n → ℂ) (x : ℕ → Λ) (p : Fin g → ℂ), (∀ k, ws k ∈ logCover L.a_le) → Tendsto (fun k => expCover a (ws k)) atTop (𝓝 0) → Tendsto (fun k => L.P (ws k) (x k)) atTop (𝓝 p) → ∃ x₀ : chartW bas B, p = chartPer bas A T0 B x₀ :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun x t ht hP => extend_mem h x t ht hP, fun ws x p hws hz hp => limit_mem h ws x p hws hz hp⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.CentrePeriods
