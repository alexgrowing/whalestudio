import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsSmoothStepSharpSlope
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtLogMinorProd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OrthoStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.LeviVA

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PoleExistence

open GlobalTheory.Up GlobalTheory.MinorRatioNear

theorem exists_det_ge (p : ℕ) {c : ℝ} (hc1 : c < 1) : ∃ δ : ℝ, 0 < δ ∧ ∀ N : Matrix (Fin p) (Fin p) ℂ,
    (∀ i j, ‖(N - 1) i j‖ < δ) → c ≤ ‖N.det‖ := by
  have hc : Continuous fun N : Fin p → Fin p → ℂ => ‖(Matrix.of N).det‖ :=
    (Continuous.matrix_det (A := fun N : Fin p → Fin p → ℂ => Matrix.of N) continuous_id).norm
  obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1
    (hc.continuousAt (x := fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j)) (1 - c) (by linarith)
  refine ⟨δ, hδ, fun N hN => ?_⟩
  have := @H (fun i j => N i j) (by
    rw [dist_pi_lt_iff hδ]; intro i
    rw [dist_pi_lt_iff hδ]; intro j
    rw [dist_eq_norm]; exact hN i j)
  have e : (Matrix.of fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j).det = 1 := Matrix.det_one
  rw [e, norm_one, Real.dist_eq, abs_lt] at this
  have e' : (Matrix.of fun i j => N i j) = N := rfl
  rw [e'] at this
  linarith [this.1]

theorem exists_block_det_ge' {r p : ℕ} (hp : p ≤ r) {c : ℝ} (hc : c < 1) : ∃ δ : ℝ, 0 < δ ∧
    ∀ g n : Matrix (Fin r) (Fin r) ℂ, g * sgnMat r p * gᴴ = sgnMat r p →
      (∀ a b, ‖(n - 1) a b‖ ≤ δ) →
      ‖(g.submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ * c ≤
        ‖((g * n).submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ := by
  obtain ⟨δ, hδ, H⟩ := exists_det_ge p hc
  refine ⟨δ / (r + 1), by positivity, fun g n h hn => ?_⟩
  set A := g.submatrix (Fin.castLE hp) (Fin.castLE hp) with hA
  set R := g.submatrix (Fin.castLE hp) (id : Fin r → Fin r) with hR
  have hu : IsUnit A.det := (det_block_ne_zero hp h).isUnit
  have e1 : (g * n).submatrix (Fin.castLE hp) (Fin.castLE hp) =
      A * (A⁻¹ * R * n.submatrix id (Fin.castLE hp)) := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
    rfl
  have e2 : R * (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) = A := by
    have : R * (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) =
        (g * 1).submatrix (Fin.castLE hp) (Fin.castLE hp) := rfl
    rw [this, Matrix.mul_one]
  have e3 : A⁻¹ * R * n.submatrix id (Fin.castLE hp) - 1 =
      A⁻¹ * R * (n - 1).submatrix id (Fin.castLE hp) := by
    have : (n - 1).submatrix id (Fin.castLE hp) = n.submatrix id (Fin.castLE hp) -
        (1 : Matrix (Fin r) (Fin r) ℂ).submatrix id (Fin.castLE hp) := rfl
    rw [this, Matrix.mul_sub, Matrix.mul_assoc A⁻¹ R (Matrix.submatrix 1 _ _), e2,
      Matrix.nonsing_inv_mul _ hu]
  have h1 := H (A⁻¹ * R * n.submatrix id (Fin.castLE hp)) fun i j => by
    rw [e3, Matrix.mul_apply]
    calc ‖∑ a, (A⁻¹ * R) i a * (n - 1).submatrix id (Fin.castLE hp) a j‖
        ≤ ∑ a : Fin r, δ / (r + 1) := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
          rw [norm_mul]
          calc _ ≤ 1 * (δ / (r + 1)) :=
                mul_le_mul (norm_entry_le_one hp h i a) (hn _ _) (norm_nonneg _) zero_le_one
            _ = _ := one_mul _
      _ < δ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
            ← mul_div_assoc, div_lt_iff₀ (by positivity)]
          nlinarith
  rw [e1, Matrix.det_mul, norm_mul]
  exact mul_le_mul_of_nonneg_left h1 (norm_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem rhX_lower_orth {r : ℕ} (X : Data E r) {x1 : Frame X.Ψ r} (h1 : IsOrth X x1) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ y in 𝓝 x1, y ∈ X.dom → ∀ x2, IsOrth X x2 → rhX X x2 x1 - t ≤ rhX X x2 y := by
  set i0 : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ with hi0
  set k : ℝ := ((Fintype.card X.Ψ : ℕ) : ℝ) with hk
  have hk0 : 0 ≤ k := Nat.cast_nonneg _
  set u : ℝ := t / (3 * k + 1) with hu
  have hu0 : 0 < u := by positivity
  obtain ⟨δ, hδ, H⟩ := exists_block_det_ge' X.p0_le (c := Real.exp (-u))
    (Real.exp_lt_one_iff.2 (by linarith))
  have ha : ∀ᶠ y in 𝓝 x1, ∀ τ, ‖dmin X.Gm y τ i0‖ < Real.exp u := by
    refine Filter.eventually_all.2 fun τ => ?_
    refine (ExtFPf.cont_dmin X τ i0).norm.continuousAt.eventually (gt_mem_nhds ?_)
    show ‖dmin X.Gm x1 τ i0‖ < _
    rw [FramePotential.norm_dmin_of_isOrth X h1]
    exact Real.one_lt_exp_iff.2 hu0
  have hb : ∀ᶠ y in 𝓝 x1, ∀ τ a b, ‖((mat x1 τ)⁻¹ * mat y τ - 1) a b‖ < δ := by
    refine Filter.eventually_all.2 fun τ => Filter.eventually_all.2 fun a =>
      Filter.eventually_all.2 fun b => ?_
    have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    have hc : Continuous fun y : Frame X.Ψ r => ‖((mat x1 τ)⁻¹ * mat y τ - 1) a b‖ :=
      (((continuous_const.matrix_mul hm).sub continuous_const).matrix_elem a b).norm
    refine hc.continuousAt.eventually (gt_mem_nhds ?_)
    show ‖((mat x1 τ)⁻¹ * mat x1 τ - 1) a b‖ < δ
    rw [Matrix.nonsing_inv_mul _ (ExF.det_ne_of_orth X h1 τ).isUnit, sub_self]
    simpa using hδ
  filter_upwards [ha, hb] with y hya hyb hy x2 h2
  have hx1 := IW.orth_mem_dom X x1 h1
  rw [rhX_eq_sum h2 hx1, rhX_eq_sum h2 hy]
  have s1 : ∑ τ : X.Ψ, Real.log ‖dmin X.Gm x1 τ i0‖ = 0 :=
    Finset.sum_eq_zero fun τ _ => by rw [FramePotential.norm_dmin_of_isOrth X h1, Real.log_one]
  have s2 : ∑ τ : X.Ψ, Real.log ‖dmin X.Gm y τ i0‖ ≤ ∑ _τ : X.Ψ, u :=
    Finset.sum_le_sum fun τ _ => by
      rw [Real.log_le_iff_le_exp (norm_pos_iff.2 (IW.dmin_ne_zero X hy τ _))]
      exact (hya τ).le
  have s3 : ∑ τ : X.Ψ, (Real.log (‖lminor ((mat x2 τ)⁻¹ * mat x1 τ) i0‖ ^ 2) - 2 * u) ≤
      ∑ τ : X.Ψ, Real.log (‖lminor ((mat x2 τ)⁻¹ * mat y τ) i0‖ ^ 2) :=
    Finset.sum_le_sum fun τ _ => by
      have hp := norm_pos_iff.2 (lminor_inv_mul_ne_zero h2 hx1 τ)
      have h3 : ‖lminor ((mat x2 τ)⁻¹ * mat x1 τ) i0‖ * Real.exp (-u) ≤
          ‖lminor ((mat x2 τ)⁻¹ * mat y τ) i0‖ := by
        have := H _ _ (isometry_of_orth X h2 h1 τ) fun a b => (hyb τ a b).le
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _
          (ExF.det_ne_of_orth X h1 τ).isUnit] at this
        exact this
      have h4 := Real.log_le_log (by positivity) h3
      rw [Real.log_mul hp.ne' (Real.exp_pos _).ne', Real.log_exp] at h4
      rw [Real.log_pow, Real.log_pow]
      push_cast
      linarith
  rw [Finset.sum_sub_distrib] at s3
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← hk] at s2 s3
  have e : t = 3 * k * u + u := by rw [hu]; field_simp
  rw [s1]
  nlinarith

theorem rhX_lower {r : ℕ} (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) {t : ℝ} (ht : 0 < t) :
    ∀ᶠ y in 𝓝 x, y ∈ X.dom → ∀ x2, IsOrth X x2 → rhX X x2 x - t ≤ rhX X x2 y := by
  obtain ⟨x1, h1, b, hb, rfl⟩ := ortho_holds r X x hx
  have hb' := ExtFPf.invF_mem X hb
  have hc : Continuous fun y : Frame X.Ψ r => rmul y (ExtFPf.invF X b) := continuous_pi fun τ => by
    have hm : Continuous fun x : Frame X.Ψ r => mat x τ := continuous_apply τ
    exact hm.matrix_mul continuous_const
  have e : rmul (rmul x1 b) (ExtFPf.invF X b) = x1 := by
    rw [ExtFPf.rmul_assoc, ExtFPf.rmul_invF X hb, ExtFPf.rmul_oneF]
  have h := rhX_lower_orth X h1 ht
  rw [← e] at h
  filter_upwards [hc.continuousAt.eventually h] with y hy hyd x2 h2
  have := hy (OntoS.dom_rmul X hyd hb') x2 h2
  rwa [rhX_rmul _ _ hb', rhX_rmul _ _ hb'] at this

open Classical in

noncomputable def poleFn {r : ℕ} (X : Data E r) (G : Subgroup (GL (Fin r) E)) (x0 : Frame X.Ψ r) (ρ0 : ℝ)
    (k : ℝ → ℝ) (x : Frame X.Ψ r) : ℝ :=
  if h : ∃ γ, γ ∈ G ∧ rhX X x0 (lact γ x) < ρ0 then k (rhX X x0 (lact h.choose x)) else 0

section
variable {r : ℕ} {X : Data E r} {G : Subgroup (GL (Fin r) E)} {x0 x : Frame X.Ψ r} {ρ0 : ℝ} {k : ℝ → ℝ}

theorem poleFn_eq (hG : FreeBall X G x0 ρ0) (hx : x ∈ X.dom) {γ : GL (Fin r) E} (hγ : γ ∈ G)
    (h : rhX X x0 (lact γ x) < ρ0) : poleFn X G x0 ρ0 k x = k (rhX X x0 (lact γ x)) := by
  have hex : ∃ γ, γ ∈ G ∧ rhX X x0 (lact γ x) < ρ0 := ⟨γ, hγ, h⟩
  rw [poleFn, dif_pos hex, hG.unique hex.choose_spec.1 hγ hx hex.choose_spec.2 h]

theorem poleFn_eq_zero {a : ℝ} (hk : ∀ u, a ≤ u → k u = 0) (h : ∀ γ ∈ G, a ≤ rhX X x0 (lact γ x)) :
    poleFn X G x0 ρ0 k x = 0 := by
  unfold poleFn
  split_ifs with hex
  · exact hk _ (h _ hex.choose_spec.1)
  · rfl

theorem poleFn_inv (hG : FreeBall X G x0 ρ0) {γ : GL (Fin r) E} (hγ : γ ∈ G) (hx : x ∈ X.dom)
    {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) :
    poleFn X G x0 ρ0 k (lact γ (rmul x b)) = poleFn X G x0 ρ0 k x := by
  have e : ∀ g : GL (Fin r) E, rhX X x0 (lact g (lact γ (rmul x b))) = rhX X x0 (lact (g * γ) x) :=
    fun g => by rw [← FundSetPf.lact_mul, FundSetPf.lact_rmul, rhX_rmul _ _ hb]
  by_cases hex : ∃ g, g ∈ G ∧ rhX X x0 (lact g x) < ρ0
  · obtain ⟨g, hg, h⟩ := hex
    have e' := e (g * γ⁻¹)
    rw [inv_mul_cancel_right] at e'
    rw [poleFn_eq hG hx hg h, poleFn_eq hG (MajInv.lact_mem_dom X (hG.isUStab hγ) (OntoS.dom_rmul X hx hb))
      (G.mul_mem hg (G.inv_mem hγ)) (by rwa [e']), e']
  · have hex' : ¬ ∃ g, g ∈ G ∧ rhX X x0 (lact g (lact γ (rmul x b))) < ρ0 := by
      rintro ⟨g, hg, h⟩
      exact hex ⟨g * γ, G.mul_mem hg hγ, by rwa [← e]⟩
    rw [poleFn, poleFn, dif_neg hex, dif_neg hex']

theorem poleFn_local (h0 : IsOrth X x0) (hG : FreeBall X G x0 ρ0) {a : ℝ} (ha : a < ρ0)
    (hk : ∀ u, a ≤ u → k u = 0) {x1 : Frame X.Ψ r} {z : V (nd X)} (hz : z ∈ OmF X x1) :
    (∃ x2, IsOrth X x2 ∧
      (fun w => poleFn X G x0 ρ0 k (cpt X x1 w)) =ᶠ[𝓝 z] fun w => k (rhX X x2 (cpt X x1 w))) ∨
    (fun w => poleFn X G x0 ρ0 k (cpt X x1 w)) =ᶠ[𝓝 z] fun _ => 0 := by
  have hO := (OntoB.isOpen_OmF X x1).mem_nhds hz
  have hc : Continuous (cpt X x1) := FundSetPf.cont_cpt X x1
  have horth : ∀ γ ∈ G, IsOrth X (lact γ⁻¹ x0) := fun γ hγ =>
    isOrth_lact_of_isUStab (hG.isUStab (G.inv_mem hγ)) h0
  by_cases hex : ∃ g, g ∈ G ∧ rhX X x0 (lact g (cpt X x1 z)) < ρ0
  · obtain ⟨g, hg, h⟩ := hex
    refine Or.inl ⟨_, horth g hg, ?_⟩
    rw [rhX_lact (hG.isUStab hg)] at h
    have hca : ContinuousAt (fun w => rhX X (lact g⁻¹ x0) (cpt X x1 w)) z :=
      ((continuousOn_rhX (horth g hg)).comp hc.continuousOn fun w hw => hw).continuousAt hO
    filter_upwards [hO, hca.eventually (gt_mem_nhds h)] with w hw hlt
    rw [poleFn_eq hG hw hg (by rwa [rhX_lact (hG.isUStab hg)]), rhX_lact (hG.isUStab hg)]
  · refine Or.inr ?_
    filter_upwards [hO, hc.continuousAt.eventually (rhX_lower X (show cpt X x1 z ∈ X.dom from hz)
      (sub_pos.2 ha))] with w hw hlow
    refine poleFn_eq_zero hk fun γ hγ => ?_
    have h1 := hlow hw _ (horth γ hγ)
    have h2 : ρ0 ≤ rhX X x0 (lact γ (cpt X x1 z)) := not_lt.1 fun h => hex ⟨γ, hγ, h⟩
    rw [rhX_lact (hG.isUStab hγ)] at h2 ⊢
    linarith

end

theorem poleEx_of_rhTr (hT : RhTr (E := E)) : PoleEx (E := E) := by
  intro r X G x0 ρ0 θ h0 hρ0 hθ hG
  obtain ⟨ε, C, hε, hερ, H⟩ := GlobalTheory.exists_cutoff_log_sharp ρ0 θ hρ0 hθ
  set D : ℝ := ((dimX X : ℕ) : ℝ) with hD
  have hD0 : 0 ≤ D := Nat.cast_nonneg _
  refine ⟨ε, D * C, hε, hερ, fun δ hδ hδ1 => ?_⟩
  obtain ⟨g, hgs, hg0, hgd, hgu, hgl⟩ := H δ hδ hδ1
  have hk0 : ∀ u, ρ0 - ε ≤ u → D * g u = 0 := fun u hu => by rw [hg0 u hu, mul_zero]
  have hks : ∀ u, 0 ≤ u → ContDiffAt ℝ ∞ (fun u => D * g u) u := fun u hu =>
    contDiffAt_const.mul (hgs.contDiffAt (Ioi_mem_nhds (by linarith)))
  have hone : ∀ x ∈ X.dom, rhX X x0 x ≤ ε →
      poleFn X G x0 ρ0 (fun u => D * g u) x = D * g (rhX X x0 x) := fun x hx hle => by
    rw [poleFn_eq hG hx G.one_mem (by rw [FundSetPf.lact_one]; linarith), FundSetPf.lact_one]
  refine ⟨poleFn X G x0 ρ0 fun u => D * g u, fun γ hγ x hx b hb => poleFn_inv hG hγ hx hb,
    fun x hx => ?_, fun x1 h1 => ⟨fun z hz => ?_, fun z hz ξ => ?_⟩, fun x hx hle => ?_,
    fun x hx ha hle => ?_⟩
  · unfold poleFn
    split_ifs with hex
    · exact mul_nonpos_of_nonneg_of_nonpos hD0 (hgd _ (rhX_nonneg h0
        (MajInv.lact_mem_dom X (hG.isUStab hex.choose_spec.1) hx))).1
    · exact le_rfl
  · have hO := (OntoB.isOpen_OmF X x1).mem_nhds hz
    refine ContDiffAt.contDiffWithinAt ?_
    rcases poleFn_local h0 hG (sub_lt_self ρ0 hε) hk0 hz with ⟨x2, h2, he⟩ | he
    · obtain ⟨hs, hp⟩ := hT r X x1 x2 h1 h2
      exact (ContDiffAt.comp z (g := fun u => D * g u) (hks _ (hp z hz).1)
        (hs.contDiffAt hO)).congr_of_eventuallyEq he
    · exact contDiffAt_const.congr_of_eventuallyEq he
  · have hO := (OntoB.isOpen_OmF X x1).mem_nhds hz
    have hL := leviRh_nonneg h1 hz ξ
    have hκ : 0 ≤ θ / ρ0 := by positivity
    unfold leviO leviM
    rcases poleFn_local h0 hG (sub_lt_self ρ0 hε) hk0 hz with ⟨x2, h2, he⟩ | he
    · obtain ⟨hs, hp⟩ := hT r X x1 x2 h1 h2
      obtain ⟨hf0, hp⟩ := hp z hz
      obtain ⟨hl, hgr⟩ := hp ξ
      unfold leviO leviM at hl
      refine le_trans ?_ (congrArg Complex.re (leviV_congr (he.fun_comp fun t : ℝ => (t : ℂ)) ξ)).ge
      have h2i : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 (le_top (a := (2 : ℕ∞)))
      have hch := ReciprocityTheory.L2DbarEstimates.H.leviChain (nd X) (fun u => D * g u) (fun w => rhX X x2 (cpt X x1 w)) z ξ
        ((hs.contDiffAt hO).of_le h2i) ((hks _ hf0).of_le h2i)
      simp only [deriv_const_mul_field'] at hch
      have hch' := congrArg Complex.re hch
      rw [Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul, Complex.ofReal_re, hl] at hch'
      refine le_trans ?_ (le_of_eq hch'.symm)
      obtain ⟨-, hd1, hd2⟩ := hgd _ hf0
      have hn := Complex.normSq_nonneg (∑ j, wd (nd X) j (fun w => ((rhX X x2 (cpt X x1 w) : ℝ) : ℂ)) z * ξ j)
      generalize Complex.normSq _ = N at hn hgr ⊢
      generalize deriv (deriv g) (rhX X x2 (cpt X x1 z)) = g2 at hd2 ⊢
      generalize deriv g (rhX X x2 (cpt X x1 z)) = g1 at hd1 hd2 ⊢
      generalize rhX X x2 (cpt X x1 z) = f at hf0 hgr hd2
      generalize leviRh X x1 z ξ = L at hL hgr ⊢
      have key : -(θ / ρ0 * L) ≤ g1 * L + g2 * N := by
        rcases le_total 0 g2 with h | h
        · nlinarith [mul_nonneg hd1 hL, mul_nonneg h hn, mul_nonneg hκ hL]
        · nlinarith [mul_le_mul_of_nonneg_right hd2 hL, mul_le_mul_of_nonpos_left hgr h]
      have := mul_le_mul_of_nonneg_left key hD0
      calc _ = D * -(θ / ρ0 * L) := by ring
        _ ≤ _ := this
        _ = _ := by ring
    · refine le_trans ?_ (congrArg Complex.re (leviV_congr (he.fun_comp fun t : ℝ => (t : ℂ)) ξ)).ge
      have e1 : ∀ k, wdb (nd X) k (fun _ => (0 : ℂ)) = fun _ => 0 := fun k => by
        funext y; simp [wdb]
      have e : (leviV (nd X) ((fun t : ℝ => (t : ℂ)) ∘ fun _ => 0) z ξ).re = 0 := by
        simp [leviV, Function.comp_def, e1, wd]
      rw [e]
      exact neg_nonpos.2 (mul_nonneg (by positivity) hL)
  · rw [hone x hx hle, ← mul_add]
    exact mul_le_mul_of_nonneg_left (hgu _ (rhX_nonneg h0 hx) hle) hD0
  · rw [hone x hx hle, ← mul_neg]
    exact mul_le_mul_of_nonneg_left (hgl _ ha) hD0

theorem poleEx_holds : PoleEx (E := E) := poleEx_of_rhTr GlobalTheory.PotentialTransfer.potential_transfer

end GlobalTheory.PoleExistence
