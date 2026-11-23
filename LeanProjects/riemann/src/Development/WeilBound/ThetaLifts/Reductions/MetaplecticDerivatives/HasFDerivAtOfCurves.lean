import Development.WeilBound.ThetaLifts.Reductions.MetaplecticDerivatives.MpFOne

noncomputable section

open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology PositivityTheory.ThKR.LL
open scoped Real ContDiff

namespace PositivityTheory.ThKR.Mp.MpG

theorem hasFDerivAt_of_curves {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {Φ : E → F} {L : E →L[ℝ] F} {x₀ : E}
    (h : ∀ (c : ℝ → E) (v : E), c 0 = x₀ → HasDerivAt c v 0 → HasDerivAt (fun t => Φ (c t)) (L v) 0) :
    HasFDerivAt Φ L x₀ := by
  classical
  rw [hasFDerivAt_iff_isLittleO_nhds_zero, Asymptotics.isLittleO_iff]
  intro ε hε
  by_contra hf
  obtain ⟨y0, hy0, hb0⟩ := exists_seq_forall_of_frequently (not_eventually.1 hf)
  have hne0 : ∀ n, y0 n ≠ 0 := fun n e => hb0 n (by simp [e])
  obtain ⟨v, -, φ, hφ, hv⟩ := (isCompact_sphere (0 : E) 1).tendsto_subseq (x := fun n => ‖y0 n‖⁻¹ • y0 n)
    (fun n => by simp [norm_smul, hne0 n])
  let y : ℕ → E := fun n => y0 (φ n)
  have hne : ∀ n, ‖y n‖ ≠ 0 := fun n => norm_ne_zero_iff.2 (hne0 _)
  let w : ℝ → E := fun t => if e : ∃ n, ‖y n‖ = t then y e.choose else t • v
  have w0 : w 0 = 0 := by
    have : ¬∃ n, ‖y n‖ = 0 := fun ⟨n, e⟩ => hne n e
    simp only [w, dif_neg this, zero_smul]
  have hw : HasDerivAt w v 0 := by
    rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
    intro δ hδ
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hv δ hδ
    have : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ m ∈ Finset.range N, t ≠ ‖y m‖ :=
      (Finset.eventually_all _).2 fun m _ => eventually_ne_nhds (hne m).symm
    filter_upwards [this] with t ht
    rw [w0, sub_zero, sub_zero]
    by_cases e : ∃ n, ‖y n‖ = t
    · have e1 := e.choose_spec
      have hm : N ≤ e.choose := not_lt.1 fun hlt => ht _ (Finset.mem_range.2 hlt) e1.symm
      have h1 := (hN _ hm).le
      rw [dist_eq_norm] at h1
      have h2 : w t - t • v = t • (‖y e.choose‖⁻¹ • y e.choose - v) := by
        rw [smul_sub, smul_smul, e1, mul_inv_cancel₀ (e1 ▸ hne _), one_smul]
        simp only [w, dif_pos e]
      rw [h2, norm_smul, mul_comm]
      exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    · simp only [w, dif_neg e, sub_self, norm_zero]
      positivity
  have h1 := (h (fun t => x₀ + w t) v (by simp [w0]) (hw.const_add x₀)).fun_sub (L.hasFDerivAt.comp_hasDerivAt 0 hw)
  rw [sub_self, hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff] at h1
  have h2 : Tendsto (fun n => ‖y n‖) atTop (𝓝 0) := by simpa using (hy0.comp hφ.tendsto_atTop).norm
  obtain ⟨n, hn⟩ := (h2.eventually (h1 hε)).exists
  have e : ∃ m, ‖y m‖ = ‖y n‖ := ⟨n, rfl⟩
  have e2 : w ‖y n‖ = y e.choose := by simp only [w, dif_pos e]
  refine hb0 (φ e.choose) ?_
  simp only [Function.comp, w0, e2, add_zero, map_zero, sub_zero, smul_zero, norm_norm] at hn
  rw [sub_right_comm]
  exact hn.trans_eq (congrArg (ε * ·) e.choose_spec.symm)

variable {l : Type} [Fintype l] [DecidableEq l]

theorem hasDerivAt_det_one {M : ℝ → l → l → ℝ} {X : l → l → ℝ} (h : HasDerivAt M X 0) (h0 : Matrix.of (M 0) = 1) :
    HasDerivAt (fun t => (Matrix.of (M t)).det) (Matrix.of X).trace 0 := by
  have hd : DifferentiableAt ℝ (fun N : l → l → ℝ => (Matrix.of N).det) (M 0) := by
    simp only [Matrix.det_apply', Matrix.of_apply]
    exact DifferentiableAt.fun_sum fun σ _ => (((contDiff_prod (n := 1) (f := fun i (N : l → l → ℝ) => N (σ i) i)
      fun i _ => contDiff_apply_apply ℝ ℝ (σ i) i).differentiable one_ne_zero) _).const_mul _
  have h1 := hd.hasFDerivAt.comp_hasDerivAt 0 h
  have h2 : HasDerivAt (fun t : ℝ => M 0 + t • X) X 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const X).const_add (M 0)
  have h3 := hd.hasFDerivAt.comp_hasDerivAt_of_eq 0 h2 (by simp)
  let p := (Matrix.det (1 + (Polynomial.X : Polynomial ℝ) • (Matrix.of X).map Polynomial.C)).divX.divX
  have h4 : HasDerivAt (fun t : ℝ => 1 + (Matrix.of X).trace * t + p.eval t * t ^ 2) (Matrix.of X).trace 0 :=
    ((((hasDerivAt_id (0 : ℝ)).const_mul _).const_add 1).fun_add
      ((p.hasDerivAt 0).fun_mul (hasDerivAt_pow 2 0))).congr_deriv (by simp)
  have h5 := h3.unique (h4.congr_of_eventuallyEq (.of_forall fun t => by
    refine Eq.trans ?_ (Matrix.det_one_add_smul t (Matrix.of X))
    rw [← h0]
    rfl))
  exact h5 ▸ h1

theorem curve {g : ℝ → (l ⊕ l) → (l ⊕ l) → ℝ} {X : (l ⊕ l) → (l ⊕ l) → ℝ} (g0 : Matrix.of (g 0) = 1)
    (hg : HasDerivAt g X 0) (f : Sch l) :
    HasDerivAt (fun t => schwartzToL2 l (sec (Matrix.of (g t)) f)) (schwartzToL2 l (Qd (Matrix.of X) f)) 0 := by
  have hd : ∀ i j : l → l ⊕ l, HasDerivAt (fun t => bl i j (Matrix.of (g t))) (bl i j (Matrix.of X)) 0 := fun i j =>
    (LinearMap.toContinuousLinearMap
      ((bl i j).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)).hasFDerivAt.comp_hasDerivAt 0 hg
  let A : ℝ → Eu l →L[ℝ] Eu l := fun t => bl Sum.inl Sum.inl (Matrix.of (g t))
  let c : ℝ → ℝ := fun t => (√|(Matrix.of (g t)).toBlocks₁₁.det|)⁻¹
  have eA : ∀ t, (A t).det = (Matrix.of (g t)).toBlocks₁₁.det := fun t => det_bl _ _ _
  have A0 : A 0 = 1 := by simp only [A, g0, block_inl_inl_one]
  have h0 : IsUnit (A 0) := A0 ▸ isUnit_one
  have hopen : ∀ᶠ u in 𝓝 0, IsUnit (A u) := (hd _ _).continuousAt.eventually (Units.isOpen.mem_nhds h0)
  have hdet : ∀ t, IsUnit (A t) → (Ring.inverse (A t)).det * (A t).det = 1 := fun t ht => by
    have := congrArg ContinuousLinearMap.det (Ring.inverse_mul_cancel _ ht)
    simpa [ContinuousLinearMap.det] using this
  have hc : ∀ t, IsUnit (A t) → c t ^ 2 = |(Ring.inverse (A t)).det| := fun t ht => by
    rw [eq_inv_of_mul_eq_one_left (hdet t ht), abs_inv, inv_pow, Real.sq_sqrt (abs_nonneg _), eA]
  have d0 : (Matrix.of (g 0)).toBlocks₁₁.det = 1 := by
    rw [← eA, A0]
    simp [ContinuousLinearMap.det]
  have c0 : c 0 = 1 := by simp only [c, d0]; simp
  have hD : HasDerivAt (fun t => (Matrix.of (g t)).toBlocks₁₁.det) (Matrix.of X).toBlocks₁₁.trace 0 :=
    hasDerivAt_det_one (M := fun t a b => g t (.inl a) (.inl b)) (X := fun a b => X (.inl a) (.inl b))
      (hasDerivAt_pi.2 fun a => hasDerivAt_pi.2 fun b => hasDerivAt_pi.1 (hasDerivAt_pi.1 hg _) _)
      (by
        ext a b
        have := congrFun (congrFun g0 (.inl a)) (.inl b)
        simpa [Matrix.one_apply] using this)
  have hcd : HasDerivAt c (-((Matrix.of X).toBlocks₁₁.trace / 2)) 0 := by
    have hp : 0 < (Matrix.of (g 0)).toBlocks₁₁.det := by rw [d0]; exact one_pos
    have h1 := (hD.sqrt hp.ne').inv (Real.sqrt_pos.2 hp).ne'
    refine (h1.congr_of_eventuallyEq ?_).congr_deriv (by simp only [d0]; simp)
    filter_upwards [hD.continuousAt.eventually (lt_mem_nhds hp)] with t ht
    simp only [c, abs_of_pos ht]
    rfl
  have h1 : HasDerivAt (fun t => Ring.inverse (A t)) (-bl Sum.inl Sum.inl (Matrix.of X)) 0 := by
    have h2 := (hasFDerivAt_ringInverse (𝕜 := ℝ) (1 : (Eu l →L[ℝ] Eu l)ˣ)).comp_hasDerivAt_of_eq 0
      (hd Sum.inl Sum.inl) A0.symm
    exact h2.congr_deriv (by
      simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mulLeftRight_apply, inv_one, Units.val_one,
        one_mul, mul_one])
  obtain ⟨Q, hQ, hQ'⟩ := ld_big h1 (hd Sum.inl Sum.inr) (hd Sum.inr Sum.inl) hcd
    (hopen.mono fun u hu => ⟨hu.ringInverse, hc u hu⟩)
  have h3 := hQ' (by rw [A0, Ring.inverse_one]) (by rw [g0, block_inl_inr_one]) (by rw [g0, block_inr_inl_one]) c0 f
  refine (hQ f).congr_deriv (congrArg _ ?_)
  rw [h3, Qd, ofReal_neg, neg_smul, sub_eq_add_neg]

end PositivityTheory.ThKR.Mp.MpG

namespace PositivityTheory.ThKR.Mp

variable {l : Type} [Fintype l] [DecidableEq l]

theorem secDer : SecDer l := by
  intro E _ _ m m' x₀ h0 hm f
  let L : ((l ⊕ l) → (l ⊕ l) → ℝ) →L[ℝ] L2 l := LinearMap.toContinuousLinearMap
    ((((schwartzToL2 l).restrictScalars ℝ).toLinearMap.comp (qdLin f)).comp (Matrix.ofLinearEquiv ℝ).toLinearMap)
  have hL : ∀ X, L X = schwartzToL2 l (Qd (Matrix.of X) f) := fun X => rfl
  have h1 : HasFDerivAt (fun g : (l ⊕ l) → (l ⊕ l) → ℝ => schwartzToL2 l (sec (Matrix.of g) f)) L (fun a b => m x₀ a b) :=
    MpG.hasFDerivAt_of_curves fun c v c0 hc => MpG.curve (by rw [c0, h0]; rfl) hc f
  have h2 : HasFDerivAt (fun x => fun a b => m x a b)
      (ContinuousLinearMap.pi fun a => ContinuousLinearMap.pi fun b => m' a b) x₀ :=
    hasFDerivAt_pi.2 fun a => hasFDerivAt_pi.2 fun b => hm a b
  refine (h1.comp x₀ h2).congr_fderiv ?_
  ext1 v
  rw [ContinuousLinearMap.comp_apply, hL, ← qd_sum]
  simp only [map_sum, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smulRight_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  exact ((schwartzToL2 l).restrictScalars ℝ).map_smul _ _

end PositivityTheory.ThKR.Mp

end
