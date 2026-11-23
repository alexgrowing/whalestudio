import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfF
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_conj_inv {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) :
    (A.map (starRingEnd ℂ))⁻¹ = A⁻¹.map (starRingEnd ℂ) := by
  have h1 := (starRingEnd ℂ).map_det A
  have h2 := (starRingEnd ℂ).map_adjugate A
  simp only [RingHom.mapMatrix_apply] at h1 h2
  rw [Matrix.inv_def, Matrix.inv_def, ← h1, ← h2]
  ext i j
  simp [Ring.inverse_eq_inv', map_inv₀]

theorem map_units_inv (τ : E →+* ℂ) (γ : GL (Fin r) E) :
    ((↑(γ⁻¹) : Matrix (Fin r) (Fin r) E).map τ) = ((γ : Matrix (Fin r) (Fin r) E).map τ)⁻¹ := by
  have h : ((↑(γ⁻¹) : Matrix (Fin r) (Fin r) E).map τ) * ((γ : Matrix (Fin r) (Fin r) E).map τ) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]
    exact Matrix.map_one _ (map_zero τ) (map_one τ)
  exact (Matrix.inv_eq_left_inv h).symm

private theorem gram_eq_lemma (X : Data E r) (τ : X.Ψ) (M : Matrix (Fin r) (Fin r) ℂ) :
    gram τ.1 X.Gm M = M.transpose * Matrix.map X.Gm τ.1 * M.map (starRingEnd ℂ) := by
  ext a b
  simp only [gram, hermC, col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  exact Finset.sum_comm

private theorem det_mat_ne_zero_of_isOrth_data (X : Data E r) {y : Frame X.Ψ r} (hy : IsOrth X y) (τ : X.Ψ) :
    (mat y τ).det ≠ 0 := by
  intro h0
  have h := congrArg Matrix.det (hy τ)
  rw [gram_eq_lemma, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, h0, zero_mul, zero_mul,
    Matrix.det_diagonal] at h
  exact (Finset.prod_ne_zero_iff.mpr fun a _ => by unfold sgn; split_ifs <;> norm_num) h.symm

theorem gM_lact_mul (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (γa γb : GL (Fin r) E) (τ : X.Ψ) :
    gM X x0 (lact γb x) τ * (gM X x0 (lact γa x) τ)⁻¹ = gM X x0 (lact (γb * γa⁻¹) x0) τ := by
  have h0 : IsUnit (mat x0 τ).det := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth_data X hx0 τ)
  have h1 : IsUnit (mat x τ).det := isUnit_iff_ne_zero.mpr (det_mat_ne_zero_of_isOrth_data X hx τ)
  show (mat x0 τ)⁻¹ * ((↑γb : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) *
      ((mat x0 τ)⁻¹ * ((↑γa : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ))⁻¹ =
    (mat x0 τ)⁻¹ * ((↑(γb * γa⁻¹) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x0 τ)
  rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ h0, Units.val_mul,
    Matrix.map_mul, map_units_inv]
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv_cancel_left _ _ h1]

theorem Mq_div (X : Data E r) {x0 x : Frame X.Ψ r} (hx0 : IsOrth X x0) (hx : IsOrth X x)
    (γa γb : GL (Fin r) E) (τ : X.Ψ) :
    Mq X x0 (lact γb x) τ * (Mq X x0 (lact γa x) τ)⁻¹ = Mq X x0 (lact (γb * γa⁻¹) x0) τ := by
  unfold Mq
  rw [Matrix.inv_submatrix_equiv, Matrix.submatrix_mul_equiv, map_conj_inv, ← Matrix.map_mul,
    gM_lact_mul X hx0 hx]

theorem kaSum (X : Data E r) {x0 : Frame X.Ψ r} (hx0 : IsOrth X x0) (hPD : PropDisc X) {s : ℝ}
    (hs : 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < s) :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ x, IsOrth X x →
      ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 s (lact γ.1 x)) ≤ C := by
  obtain ⟨c, hc, hsep⟩ := sep X hx0 hPD
  set f := Fintype.card X.Ψ with hf
  set eΨ : Fin f ≃ X.Ψ := (Fintype.equivFin X.Ψ).symm with heΨ
  have hs' : 2 * (f : ℝ) * (((r - X.p0 + X.p0 : ℕ) : ℝ)) ^ 2 < s := by
    rw [Nat.sub_add_cancel X.p0_le, hf, Fintype.card_coe]; exact hs
  obtain ⟨C, hC, hbd⟩ := sumBd_sum (p := r - X.p0) (q := X.p0) (f := f) hs' hc
  refine ⟨C, hC, fun x hx => ?_⟩
  set xx : X.Γ → Fin f → Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ :=
    fun γ k => Mq X x0 (lact γ.1 x) (eΨ k) with hxx
  have hU : ∀ a k, IsUpq (xx a k) := fun a k =>
    Mq_isUpq X hx0 (PairUnfoldPf.isOrth_lact X a.2 hx) _
  have hS : ∀ a b : X.Γ, a ≠ b → ∃ k i j,
      c ≤ ‖(xx b k * (xx a k)⁻¹) i j -
        (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ) i j‖ := by
    intro a b hab
    have hδ : b.1 * a.1⁻¹ ∈ X.Γ := X.Γ.mul_mem b.2 (X.Γ.inv_mem a.2)
    have hne : b.1 * a.1⁻¹ ≠ 1 := fun h => hab (Subtype.ext (mul_inv_eq_one.1 h).symm)
    obtain ⟨τ, i', j', hij⟩ := hsep _ hδ hne
    refine ⟨eΨ.symm τ, (eS X).symm i', (eS X).symm j', ?_⟩
    simp only [hxx, Equiv.apply_symm_apply]
    rw [Mq_div X hx0 hx]
    unfold Mq
    rw [Matrix.submatrix_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Matrix.map_apply]
    have h1 : (1 : Matrix (Fin (r - X.p0) ⊕ Fin X.p0) (Fin (r - X.p0) ⊕ Fin X.p0) ℂ)
        ((eS X).symm i') ((eS X).symm j') = starRingEnd ℂ ((1 : Matrix (Fin r) (Fin r) ℂ) i' j') := by
      simp [Matrix.one_apply, apply_ite]
    rw [h1, ← map_sub, Complex.norm_conj]
    exact hij
  have hsum := hbd X.Γ xx hU hS
  refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) hsum
  rw [kaY_orth X hx0 (PairUnfoldPf.isOrth_lact X γ.2 hx) s]
  congr 1
  exact (Fintype.prod_equiv eΨ _ _ (fun k => rfl)).symm

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cs_tsum {ι : Type*} (u v : ι → ℝ≥0∞) :
    ∑' i, u i * v i ≤ (∑' i, u i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∑' i, v i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ i ∈ s, u i * v i
      ≤ (∑ i ∈ s, u i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) * (∑ i ∈ s, v i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
        first
          | exact ENNReal.inner_le_Lp_mul_Lq s u v .two_two
          | exact ENNReal.inner_le_Lp_mul_Lq s u v Real.HolderConjugate.two_two
    _ ≤ _ := by
        gcongr
        · exact ENNReal.sum_le_tsum s
        · exact ENNReal.sum_le_tsum s

theorem cs_sq {ι : Type*} (a k : ι → ℝ≥0∞) (hk0 : ∀ i, k i ≠ 0) (hkt : ∀ i, k i ≠ ⊤) :
    (∑' i, a i) ^ 2 ≤ (∑' i, a i ^ 2 / k i) * ∑' i, k i := by
  have hh : ∀ S : ℝ≥0∞, (S ^ (1 / 2 : ℝ)) ^ 2 = S := fun S => by
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hsq : ∀ i, (k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = k i := fun i => by
    rw [← ENNReal.rpow_mul]
    norm_num
  have hne0 : ∀ i, k i ^ (1 / 2 : ℝ) ≠ 0 := fun i =>
    (ENNReal.rpow_pos (pos_iff_ne_zero.2 (hk0 i)) (hkt i)).ne'
  have hneT : ∀ i, k i ^ (1 / 2 : ℝ) ≠ ⊤ := fun i =>
    ENNReal.rpow_ne_top_of_nonneg (by norm_num) (hkt i)
  have hu : ∀ i, a i = (a i / k i ^ (1 / 2 : ℝ)) * k i ^ (1 / 2 : ℝ) := fun i =>
    (ENNReal.div_mul_cancel (hne0 i) (hneT i)).symm
  have hu2 : ∀ i, (a i / k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = a i ^ 2 / k i := fun i => by
    rw [ENNReal.div_rpow_of_nonneg _ _ (by norm_num), hsq, ENNReal.rpow_two]
  calc (∑' i, a i) ^ 2 = (∑' i, (a i / k i ^ (1 / 2 : ℝ)) * k i ^ (1 / 2 : ℝ)) ^ 2 := by
        rw [tsum_congr fun i => hu i]
    _ ≤ ((∑' i, (a i / k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ) *
          (∑' i, (k i ^ (1 / 2 : ℝ)) ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ 2 := by
        gcongr
        exact cs_tsum _ _
    _ = (∑' i, a i ^ 2 / k i) * ∑' i, k i := by
        simp only [hu2, hsq]
        rw [mul_pow, hh, hh]

theorem cont_mat (X : Data E r) (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => mat y τ := by
  refine continuous_matrix fun i j => ?_
  simp only [mat, Matrix.of_apply]
  fun_prop

theorem cont_dmin (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun y : Frame X.Ψ r => dmin X.Gm y τ i := by
  unfold dmin lminor gram
  refine Continuous.matrix_det (Continuous.matrix_submatrix ?_ _ _)
  refine continuous_matrix fun a b => ?_
  unfold hermC col mat
  simp only [Matrix.of_apply, Matrix.mul_apply]
  fun_prop

theorem cont_lminor_gM (X : Data E r) (x0 : Frame X.Ψ r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun y : Frame X.Ψ r => lminor (gM X x0 y τ) i := by
  unfold lminor gM
  exact Continuous.matrix_det (Continuous.matrix_submatrix (continuous_const.matrix_mul (cont_mat X τ)) _ _)

theorem meas_kaY (X : Data E r) (x0 : Frame X.Ψ r) (bb : ℝ) : Measurable (kaY X x0 bb) := by
  unfold kaY rhY
  refine Real.measurable_exp.comp (measurable_const.mul (Finset.measurable_sum _ fun τ _ => ?_).neg)
  exact ((cont_dmin X τ _).measurable.norm.log).sub
    (measurable_const.mul (cont_lminor_gM X x0 τ _).measurable.norm.log)

theorem ff_holds : FFStatement (E := E) := by
  intro r X x0 la W bb F P H FF hFF
  obtain ⟨hx0, hPD, hW, -, hbb, -, hA, hP, hPF⟩ := H
  classical
  obtain ⟨D⟩ := ExtFPf.luData_of lu_holds X x0 hx0
  have hs : 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 < bb := by
    have : 0 ≤ 2 * (X.Ψ.card : ℝ) * (r : ℝ) ^ 2 := by positivity
    linarith
  obtain ⟨C1, hC1, hsum⟩ := kaSum X hx0 hPD hs
  have hsumY : ∀ y ∈ X.dom, ∑' γ : X.Γ, ENNReal.ofReal (kaY X x0 bb (lact γ.1 y)) ≤ C1 := by
    intro y hy
    have hb := FrameDegreeData.bOf_mem X hy
    have ho : IsOrth X (rmul y (FrameDegreeData.bOf X y)) := FrameDegreeData.ortho_bOf X hy
    refine le_trans (le_of_eq (tsum_congr fun γ => ?_)) (hsum _ ho)
    rw [lact_rmul' γ.1 y (FrameDegreeData.bOf X y),
      kaY_rmul X hx0 ((PairUnfoldPf.lact_mem_dom_iff X γ.2 y).2 hy) hb]
  set Pd := X.dom.indicator P with hPd
  have hPdm : Measurable Pd := PairUnfoldPf.meas_indC X hP.1.continuousOn
  set ψ : Frame X.Ψ r → ℝ≥0∞ := fun y => ‖Pd y‖ₑ ^ 2 * W y / ENNReal.ofReal (kaY X x0 bb y) with hψ
  have hψm : Measurable ψ :=
    ((hPdm.enorm.pow_const 2).mul hW.1).div (meas_kaY X x0 bb).ennreal_ofReal
  have hψB : ∀ y ∈ X.dom, ∀ b ∈ Bor X.Ψ r, ψ (rmul y b) = ψ y := by
    intro y hy b hb
    have hyb : rmul y b ∈ X.dom := rmulDom X hb hy
    simp only [hψ, hPd, Set.indicator_of_mem hyb, Set.indicator_of_mem hy, hP.2 y hy b hb,
      hW.2.1 y hy b hb, kaY_rmul X hx0 hy hb]
    have hpos : 0 < ‖bchar la b‖ ^ 2 := pow_pos (norm_pos_iff.2 (bchar_ne X la hb)) 2
    have h0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := (ENNReal.ofReal_pos.2 hpos).ne'
    have ht : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
    have hc : ‖bchar la b‖ₑ ^ 2 = ENNReal.ofReal (‖bchar la b‖ ^ 2) := by
      rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _)]
    rw [enorm_mul, mul_pow, hc]
    congr 1
    rw [ENNReal.div_eq_inv_mul]
    calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ‖P y‖ₑ ^ 2 * ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W y)
        = (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) *
            (‖P y‖ₑ ^ 2 * W y) := by ring
      _ = ‖P y‖ₑ ^ 2 * W y := by rw [ENNReal.mul_inv_cancel h0 ht, one_mul]
  have hpt : ∀ z ∈ FF, ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ≤
      C1 * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) := by
    intro z hz
    have hy : cpt X x0 z ∈ X.dom := hFF.2.1 hz
    have hk0 : ∀ γ : X.Γ, ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z))) ≠ 0 := fun γ =>
      (ENNReal.ofReal_pos.2 (kaY_pos _ _ _ _)).ne'
    have hkt : ∀ γ : X.Γ, ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z))) ≠ ⊤ := fun _ =>
      ENNReal.ofReal_ne_top
    have hcs := cs_sq (fun γ : X.Γ => ‖P (lact γ.1 (cpt X x0 z))‖ₑ)
      (fun γ => ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z)))) hk0 hkt
    have h1 : ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) ≤
        (∑' γ : X.Γ, ‖P (lact γ.1 (cpt X x0 z))‖ₑ) ^ 2 := by
      rw [ENNReal.ofReal_pow (norm_nonneg _)]
      exact pow_le_pow_left₀ zero_le (enorm_poin_le X la P _) 2
    have h2 : ∀ γ : X.Γ, ‖P (lact γ.1 (cpt X x0 z))‖ₑ ^ 2 /
        ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z))) * W (cpt X x0 z) =
          ψ (lact γ.1 (cpt X x0 z)) := by
      intro γ
      have hγy : lact γ.1 (cpt X x0 z) ∈ X.dom := (PairUnfoldPf.lact_mem_dom_iff X γ.2 _).2 hy
      simp only [hψ, hPd, Set.indicator_of_mem hγy, hW.2.2 γ.1 γ.2 _ hy]
      rw [ENNReal.mul_div_right_comm]
    calc ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z)
        ≤ ((∑' γ : X.Γ, ‖P (lact γ.1 (cpt X x0 z))‖ₑ ^ 2 /
            ENNReal.ofReal (kaY X x0 bb (lact γ.1 (cpt X x0 z)))) * C1) * W (cpt X x0 z) :=
          mul_le_mul_of_nonneg_right
            (h1.trans (hcs.trans (mul_le_mul_of_nonneg_left (hsumY _ hy) zero_le))) zero_le
      _ = C1 * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) := by
          rw [← tsum_congr h2, ENNReal.tsum_mul_right]; ring
  have hmeasγ : ∀ γ : X.Γ, AEMeasurable (fun z => ψ (lact γ.1 (cpt X x0 z)))
      ((muF X x0).restrict FF) := fun γ =>
    (hψm.comp ((PairUnfoldPf.lact_cont X γ.1).comp (PairUnfoldPf.cpt_cont X x0)).measurable).aemeasurable
  have hunf := PairUnfoldPf.lunfold D FF measInv_holds hx0 hFF ψ hψm hψB
  have hrhs : ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, ENNReal.ofReal (‖F z‖ ^ 2 / kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_congr_ae ?_
    filter_upwards [ExtFPf.ae_OmF] with z hz
    have hyd : cpt X x0 z ∈ X.dom := hz
    simp only [hψ, hPd, Set.indicator_of_mem hyd, hPF z hz, kaY_cpt X hx0]
    rw [ENNReal.ofReal_div_of_pos (by unfold kaF; exact Real.exp_pos _), ENNReal.ofReal_pow (norm_nonneg _),
      ofReal_norm, ENNReal.mul_div_right_comm]
  unfold InFF
  calc ∫⁻ z in FF, ENNReal.ofReal (‖poin X la P (cpt X x0 z)‖ ^ 2) * W (cpt X x0 z) ∂muF X x0
      ≤ ∫⁻ z in FF, C1 * ∑' γ : X.Γ, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := setLIntegral_mono' hFF.1 hpt
    _ = C1 * ∑' γ : X.Γ, ∫⁻ z in FF, ψ (lact γ.1 (cpt X x0 z)) ∂muF X x0 := by
        rw [lintegral_const_mul' _ _ hC1.ne, lintegral_tsum hmeasγ]
    _ = C1 * ∫⁻ z, ψ (cpt X x0 z) ∂muF X x0 := by rw [hunf]
    _ < ⊤ := ENNReal.mul_lt_top hC1 (by rw [hrhs]; exact hA)

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
