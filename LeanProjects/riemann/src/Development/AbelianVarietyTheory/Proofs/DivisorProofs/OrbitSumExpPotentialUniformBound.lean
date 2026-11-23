import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralInvariantChartSetLeMulFundamentalSet
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MulSgnMatMulConjTranspose
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ExistsMixedProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory
open scoped ENNReal Matrix

namespace GlobalTheory.OrbitSum

open GlobalTheory.MinorRatioNear

theorem norm_lminor_inv {r p : ℕ} (hp : p ≤ r) {g : Matrix (Fin r) (Fin r) ℂ}
    (h : g * sgnMat r p * gᴴ = sgnMat r p) :
    ‖lminor g⁻¹ ⟨p, Nat.lt_succ_of_le hp⟩‖ = ‖lminor g ⟨p, Nat.lt_succ_of_le hp⟩‖ := by
  have hinv : g⁻¹ = sgnMat r p * gᴴ * sgnMat r p := by
    refine Matrix.inv_eq_right_inv ?_
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h, sgnMat_mul_self]
  have hsub : (sgnMat r p * gᴴ * sgnMat r p).submatrix (Fin.castLE hp) (Fin.castLE hp) =
      (g.submatrix (Fin.castLE hp) (Fin.castLE hp))ᴴ := by
    ext a b
    have ha : ((Fin.castLE hp a : Fin r) : ℕ) < p := a.isLt
    have hb : ((Fin.castLE hp b : Fin r) : ℕ) < p := b.isLt
    simp only [Matrix.submatrix_apply, Matrix.diagonal_mul, Matrix.mul_diagonal, sgnMat,
      Matrix.conjTranspose_apply, sgn, if_pos ha, if_pos hb]
    simp
  unfold lminor
  rw [hinv]
  exact (congrArg (fun M => ‖M.det‖) hsub).trans (by rw [Matrix.det_conjTranspose, norm_star])

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem rhX_symm (X : Data E r) {x y : Frame X.Ψ r} (hx : IsOrth X x) (hy : IsOrth X y) :
    GlobalTheory.Up.rhX X x y = GlobalTheory.Up.rhX X y x := by
  unfold GlobalTheory.Up.rhX
  congr 2
  refine Finset.prod_congr rfl fun τ _ => ?_
  have hux : IsUnit (mat x τ).det := (ExF.det_ne_of_orth X hx τ).isUnit
  have e : (mat y τ)⁻¹ * mat x τ = ((mat x τ)⁻¹ * mat y τ)⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hux]
  rw [IC.norm_dmin_orth X hx, IC.norm_dmin_orth X hy, e,
    norm_lminor_inv X.p0_le (isometry_of_orth X hx hy τ)]

theorem exists_det_le_two (p : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ N : Matrix (Fin p) (Fin p) ℂ,
    (∀ i j, ‖(N - 1) i j‖ < δ) → ‖N.det‖ ≤ 2 := by
  have hc : Continuous fun N : Fin p → Fin p → ℂ => ‖(Matrix.of N).det‖ :=
    (Continuous.matrix_det (A := fun N : Fin p → Fin p → ℂ => Matrix.of N) continuous_id).norm
  obtain ⟨δ, hδ, H⟩ := Metric.continuousAt_iff.1
    (hc.continuousAt (x := fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j)) 1 (by norm_num)
  refine ⟨δ, hδ, fun N hN => ?_⟩
  have := @H (fun i j => N i j) (by
    rw [dist_pi_lt_iff hδ]; intro i
    rw [dist_pi_lt_iff hδ]; intro j
    rw [dist_eq_norm]; exact hN i j)
  have e : (Matrix.of fun i j => (1 : Matrix (Fin p) (Fin p) ℂ) i j).det = 1 := Matrix.det_one
  rw [e, norm_one, Real.dist_eq, abs_lt] at this
  have e' : (Matrix.of fun i j => N i j) = N := rfl
  rw [e'] at this
  linarith [this.2]

theorem exists_block_det_le {r p : ℕ} (hp : p ≤ r) : ∃ δ : ℝ, 0 < δ ∧
    ∀ g n : Matrix (Fin r) (Fin r) ℂ, g * sgnMat r p * gᴴ = sgnMat r p →
      (∀ a b, ‖(n - 1) a b‖ ≤ δ) →
      ‖((g * n).submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ ≤
        2 * ‖(g.submatrix (Fin.castLE hp) (Fin.castLE hp)).det‖ := by
  obtain ⟨δ, hδ, H⟩ := exists_det_le_two p
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
  nlinarith [norm_nonneg A.det]

theorem harnack (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∃ K : ℝ, ∀ x x1 : Frame X.Ψ r, IsOrth X x → IsOrth X x1 → ∀ z : V (nd X),
      ‖z‖ < ρ → z ∈ OmF X x1 ∧ GlobalTheory.Up.rhX X x (cpt X x1 z) ≤ GlobalTheory.Up.rhX X x x1 + K := by
  set i0 : Fin (r + 1) := ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ with hi0
  obtain ⟨δ, hδ, H⟩ := exists_block_det_le (r := r) X.p0_le

  have hc : Continuous fun z : V (nd X) => fun τ : X.Ψ => dmin X.Gm (cpt X x0 z) τ i0 :=
    continuous_pi fun τ => (ExtFPf.cont_dmin X τ i0).comp (FundSetPf.cont_cpt (X := X) (x0 := x0))
  obtain ⟨ρ1, hρ1, H1⟩ := Metric.continuousAt_iff.1 (hc.continuousAt (x := 0)) (1 / 2) (by norm_num)

  have h00 : (0 : V (nd X)) ∈ OmF X x0 := by
    show cpt X x0 0 ∈ X.dom
    rw [IW.cpt_zero]; exact IW.orth_mem_dom X x0 h0
  obtain ⟨ρ2, hρ2, H2⟩ := Metric.isOpen_iff.1 (OntoB.isOpen_OmF X x0) 0 h00
  refine ⟨min δ (min ρ1 ρ2), lt_min hδ (lt_min hρ1 hρ2), X.Ψ.card * Real.log 8,
    fun x x1 hx hx1 z hz => ?_⟩
  have hzδ : ‖z‖ ≤ δ := hz.le.trans (min_le_left _ _)
  have hz1 : ‖z‖ < ρ1 := hz.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hz2 : ‖z‖ < ρ2 := hz.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hzO : z ∈ OmF X x1 := by
    rw [GlobalTheory.Up.PoleValue.OmF_eq h0 hx1]
    exact H2 (mem_ball_zero_iff.2 hz2)
  refine ⟨hzO, ?_⟩
  have hd : ∀ τ : X.Ψ, 1 / 2 ≤ ‖dmin X.Gm (cpt X x1 z) τ i0‖ := by
    intro τ
    have hdist := H1 (by rwa [dist_zero_right])
    rw [dist_pi_lt_iff (by norm_num)] at hdist
    have h' := hdist τ
    rw [dist_eq_norm] at h'
    have h0' : ‖dmin X.Gm (cpt X x0 0) τ i0‖ = 1 := by
      rw [IW.cpt_zero]; exact IC.norm_dmin_orth X h0 τ i0
    rw [dmin_cpt_eq X h0 hx1]
    have := norm_sub_norm_le (dmin X.Gm (cpt X x0 0) τ i0) (dmin X.Gm (cpt X x0 z) τ i0)
    rw [norm_sub_rev] at h'
    linarith

  set a : X.Ψ → ℝ := fun τ => ‖dmin X.Gm x1 τ i0‖ / ‖lminor ((mat x τ)⁻¹ * mat x1 τ) i0‖ ^ 2
    with ha
  set b : X.Ψ → ℝ := fun τ =>
    ‖dmin X.Gm (cpt X x1 z) τ i0‖ / ‖lminor ((mat x τ)⁻¹ * mat (cpt X x1 z) τ) i0‖ ^ 2 with hb
  have hapos : ∀ τ, 0 < a τ := fun τ => by
    have := norm_pos_iff.2 (det_block_ne_zero X.p0_le (isometry_of_orth X hx hx1 τ))
    simp only [ha, IC.norm_dmin_orth X hx1]
    positivity
  have hab : ∀ τ, 1 / 8 * a τ ≤ b τ := fun τ => by
    have hiso := isometry_of_orth X hx hx1 τ
    have hL : 0 < ‖lminor ((mat x τ)⁻¹ * mat x1 τ) i0‖ :=
      norm_pos_iff.2 (det_block_ne_zero X.p0_le hiso)
    have hU : ‖lminor ((mat x τ)⁻¹ * mat (cpt X x1 z) τ) i0‖ ≤
        2 * ‖lminor ((mat x τ)⁻¹ * mat x1 τ) i0‖ := by
      rw [ExF.mat_cpt, ← Matrix.mul_assoc]
      exact H _ _ hiso fun a b => (norm_nmat_sub_one_le X z τ a b).trans hzδ
    have hU0 : 0 < ‖lminor ((mat x τ)⁻¹ * mat (cpt X x1 z) τ) i0‖ := by
      have hzd : cpt X x1 z ∈ X.dom := hzO
      exact norm_pos_iff.2 (GlobalTheory.Up.lminor_inv_mul_ne_zero hx hzd τ)
    simp only [ha, hb, IC.norm_dmin_orth X hx1]
    have hd' := hd τ
    calc 1 / 8 * (1 / ‖lminor ((mat x τ)⁻¹ * mat x1 τ) i0‖ ^ 2)
        = (1 / 2) / (2 * ‖lminor ((mat x τ)⁻¹ * mat x1 τ) i0‖) ^ 2 := by field_simp; ring
      _ ≤ ‖dmin X.Gm (cpt X x1 z) τ i0‖ / (2 * ‖lminor ((mat x τ)⁻¹ * mat x1 τ) i0‖) ^ 2 := by
          gcongr
      _ ≤ _ := div_le_div_of_nonneg_left (by linarith) (pow_pos hU0 2)
          (pow_le_pow_left₀ hU0.le hU 2)
  have hprod : (1 / 8 : ℝ) ^ X.Ψ.card * ∏ τ, a τ ≤ ∏ τ, b τ := by
    have hc8 : (∏ _τ : X.Ψ, (1 / 8 : ℝ)) = (1 / 8) ^ X.Ψ.card := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_coe]
    rw [← hc8, ← Finset.prod_mul_distrib]
    exact Finset.prod_le_prod (fun τ _ => by have := hapos τ; positivity) fun τ _ => hab τ
  have hA : 0 < ∏ τ, a τ := Finset.prod_pos fun τ _ => hapos τ
  have hl := Real.log_le_log (by positivity) hprod
  rw [Real.log_mul (by positivity) hA.ne', Real.log_pow] at hl
  have h8 : Real.log (1 / 8 : ℝ) = -Real.log 8 := by rw [one_div, Real.log_inv]
  rw [h8] at hl
  show -Real.log (∏ τ, b τ) ≤ -Real.log (∏ τ, a τ) + X.Ψ.card * Real.log 8
  linarith

end GlobalTheory.OrbitSum

namespace GlobalTheory.OrbitSum

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem finite_mult (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) (hPD : PropDisc X) :
    ∃ ρ : ℝ, 0 < ρ ∧ {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ Metric.ball (0 : V (nd X)) ρ,
      ∃ z' ∈ Metric.ball (0 : V (nd X)) ρ, ∃ b ∈ Bor X.Ψ r,
        lact γ (cpt X x0 z) = rmul (cpt X x0 z') b}.Finite := by
  have hd := IW.orth_mem_dom X x0 h0
  obtain ⟨U, hU, U', hU', hfin⟩ := hPD x0 hd x0 hd
  have hc := (FundSetPf.cont_cpt X x0).continuousAt (x := 0)
  rw [ContinuousAt, IW.cpt_zero] at hc
  obtain ⟨ρ, hρ, hball⟩ := Metric.mem_nhds_iff.1 (hc (Filter.inter_mem hU hU'))
  refine ⟨ρ, hρ, hfin.subset ?_⟩
  rintro γ ⟨hγ, z, hz, z', hz', b, hb, e⟩
  exact ⟨hγ, _, (hball hz).1, _, (hball hz').2, b, hb, e⟩

theorem muF_ball_ne_zero (X : Data E r) {x0 : Frame X.Ψ r} (h0 : IsOrth X x0) {ρ : ℝ} (hρ : 0 < ρ) :
    muF X x0 (Metric.ball 0 ρ) ≠ 0 := by
  have hO := OntoB.isOpen_OmF X x0
  have h00 : (0 : V (nd X)) ∈ OmF X x0 := by
    show cpt X x0 0 ∈ X.dom
    rw [IW.cpt_zero]; exact IW.orth_mem_dom X x0 h0
  unfold muF
  rw [Ne, withDensity_apply_eq_zero' (OntoC.measurable_densF X x0).aemeasurable,
    Measure.restrict_apply' hO.measurableSet]
  have hsub : Metric.ball (0 : V (nd X)) ρ ∩ OmF X x0 ⊆
      {z | ENNReal.ofReal (densF X x0 z) ≠ 0} ∩ Metric.ball 0 ρ ∩ OmF X x0 := by
    rintro z ⟨h1, h2⟩
    exact ⟨⟨by simpa using OntoB.densF_pos h2, h1⟩, h2⟩
  intro h
  have h3 := measure_mono_null hsub h
  have h4 : (volume (Metric.ball (0 : V (nd X)) ρ ∩ OmF X x0)) ≠ 0 :=
    ((Metric.isOpen_ball.inter hO).measure_pos volume ⟨0, Metric.mem_ball_self hρ, h00⟩).ne'
  exact h4 h3

theorem orbitSum_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (x0 : Frame X.Ψ r), IsOrth X x0 → PropDisc X → ∀ s : ℝ, 0 < s → (∃ I : ℝ≥0∞, I < ⊤ ∧ ∀ x1 : Frame X.Ψ r, IsOrth X x1 → ∫⁻ z, ENNReal.ofReal (Real.exp (-(s * rhF X x1 z))) ∂muF X x1 ≤ I) → ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x → ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) ≤ C := by
  intro E _ _ _ r X x0 h0 hPD s hs ⟨I, hI, hIb⟩
  classical
  haveI := FundSetPf.countable_GL (E := E) (r := r)
  obtain ⟨ρ1, hρ1, K, hH⟩ := harnack X h0
  obtain ⟨ρ2, hρ2, hfin⟩ := finite_mult X h0 hPD
  obtain ⟨FF, hFF⟩ := fundSet_holds r X x0 h0 hPD
  set ρ := min ρ1 ρ2 with hρdef
  have hρ : 0 < ρ := lt_min hρ1 hρ2
  set A : Set (V (nd X)) := Metric.ball 0 ρ with hAdef
  have hAO : A ⊆ OmF X x0 := fun z hz =>
    (hH x0 x0 h0 h0 z (lt_of_lt_of_le (mem_ball_zero_iff.1 hz) (min_le_left _ _))).1
  set S : Set (GL (Fin r) E) := {γ : GL (Fin r) E | γ ∈ X.Γ ∧ ∃ z ∈ A, ∃ z' ∈ A, ∃ b ∈ Bor X.Ψ r,
    lact γ (cpt X x0 z) = rmul (cpt X x0 z') b} with hSdef
  have hSfin : S.Finite := by
    refine hfin.subset ?_
    have hb : A ⊆ Metric.ball 0 ρ2 := Metric.ball_subset_ball (min_le_right _ _)
    rintro γ ⟨hγ, z, hz, z', hz', b, hb', e⟩
    exact ⟨hγ, z, hb hz, z', hb hz', b, hb', e⟩
  set m : ℝ≥0∞ := (S.encard : ℝ≥0∞) with hmdef
  have hm : m ≠ ⊤ := by
    rw [hmdef]
    exact ENat.toENNReal_ne_top.2 hSfin.encard_lt_top.ne
  set v : ℝ≥0∞ := muF X x0 A with hvdef
  have hv : v ≠ 0 := muF_ball_ne_zero X h0 hρ
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (s * K)) with hkdef
  refine ⟨k * m * I / v, ENNReal.div_lt_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top hm) hI.ne) hv, fun x hx => ?_⟩

  set φ : Frame X.Ψ r → ℝ≥0∞ := fun y => ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x y))) with hφdef
  have hφm : Measurable φ := ENNReal.measurable_ofReal.comp
    (Real.measurable_exp.comp ((GlobalTheory.Up.measurable_rhX hx).const_mul s).neg)
  have hφB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul y b) = φ y := fun y _ b hb => by
    simp only [hφdef, GlobalTheory.Up.rhX_rmul x y hb]
  set G : Frame X.Ψ r → ℝ≥0∞ := fun y => ∑' δ : X.Γ, φ (lact δ.1 y) with hGdef
  have hGm : Measurable G := Measurable.ennreal_tsum fun δ =>
    hφm.comp (GlobalTheory.Unfold.continuous_lact X δ.1).measurable
  have hGB : ∀ b ∈ Bor X.Ψ r, ∀ y ∈ X.dom, G (rmul y b) = G y := fun b hb y _ => by
    simp only [hGdef, hφdef, FundSetPf.lact_rmul, GlobalTheory.Up.rhX_rmul x _ hb]
  have hGΓ : ∀ γ ∈ X.Γ, ∀ y ∈ X.dom, G (lact γ y) = G y := fun γ hγ y _ => by
    simp only [hGdef]
    rw [← (Equiv.mulRight (⟨γ, hγ⟩ : X.Γ)).tsum_eq (fun δ : X.Γ => φ (lact δ.1 y))]
    refine tsum_congr fun δ => ?_
    show φ (lact δ.1 (lact γ y)) = φ (lact ((δ * ⟨γ, hγ⟩ : X.Γ) : GL (Fin r) E) y)
    rw [Subgroup.coe_mul, FundSetPf.lact_mul]

  have hsum : ∑' γ : X.Γ, ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))) = G x0 := by
    simp only [hGdef]
    rw [← (Equiv.inv X.Γ).tsum_eq
      (fun γ : X.Γ => ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact γ.1 x)))))]
    refine tsum_congr fun δ => ?_
    show ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x0 (lact (δ.1)⁻¹ x)))) =
      ENNReal.ofReal (Real.exp (-(s * GlobalTheory.Up.rhX X x (lact δ.1 x0))))
    rw [GlobalTheory.Up.rhX_lact (X.Γ_stab _ (X.Γ.inv_mem δ.2)), inv_inv,
      rhX_symm X (GlobalTheory.Unfold.isOrth_lact X h0 δ.2) hx]

  have hHar : ∀ z ∈ A, G x0 ≤ k * G (cpt X x0 z) := by
    intro z hz
    have hz' : ‖z‖ < ρ1 := lt_of_lt_of_le (mem_ball_zero_iff.1 hz) (min_le_left _ _)
    simp only [hGdef]
    rw [← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun δ => ?_
    have ho := GlobalTheory.Unfold.isOrth_lact X h0 δ.2
    have h := (hH x _ hx ho z hz').2
    rw [← GlobalTheory.Unfold.cpt_lact, hkdef, hφdef, ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← Real.exp_add]
    refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
    nlinarith

  have h1 : G x0 * v ≤ k * ∫⁻ z in A, G (cpt X x0 z) ∂muF X x0 := by
    rw [hvdef, ← setLIntegral_const, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine setLIntegral_mono' measurableSet_ball fun z hz => hHar z hz
  have h2 : ∫⁻ z in A, G (cpt X x0 z) ∂muF X x0 ≤ m * ∫⁻ z in FF, G (cpt X x0 z) ∂muF X x0 :=
    GlobalTheory.Unfold.lintegral_chart_le_mul_fundSet E r X x0 x0 FF A m G h0 h0 hFF measurableSet_ball hAO
      hGm hGΓ hGB le_rfl
  have h3 : ∫⁻ z in FF, G (cpt X x0 z) ∂muF X x0 = ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 :=
    (GlobalTheory.Unfold.lintegral_unfold measInv_holds r X x0 h0 FF hFF φ hφm hφB).symm
  have h4 : ∫⁻ z, φ (cpt X x0 z) ∂muF X x0 ≤ I := by
    rw [measInv_holds r X x0 x h0 hx φ hφm hφB]
    refine le_trans (le_of_eq (lintegral_congr_ae ?_)) (hIb x hx)
    filter_upwards [ExtFPf.ae_OmF (x0 := x)] with z hz
    simp only [hφdef, GlobalTheory.Up.rhX_cpt hx hz]
  rw [hsum, ENNReal.le_div_iff_mul_le (Or.inl hv) (Or.inr (ENNReal.mul_ne_top (ENNReal.mul_ne_top
    ENNReal.ofReal_ne_top hm) hI.ne))]
  calc G x0 * v ≤ k * ∫⁻ z in A, G (cpt X x0 z) ∂muF X x0 := h1
    _ ≤ k * (m * I) := by
        gcongr
        rw [← h3] at h4
        exact h2.trans (by gcongr)
    _ = k * m * I := by ring

end GlobalTheory.OrbitSum
