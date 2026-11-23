import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PoinStatementPfC
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MeasurableEmbeddingRotAbout

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem diff_coord {n : ℕ} (i : Fin n) : Differentiable ℂ fun v : V n => v i := by
  exact (EuclideanSpace.proj (𝕜 := ℂ) i).differentiable

theorem diff_nmat (X : Data E r) (τ : X.Ψ) (a b : Fin r) :
    Differentiable ℂ fun z : V (nd X) => nmat X z τ a b := by
  unfold nmat
  by_cases h : b < a
  · simp only [h, dif_pos]
    exact diff_coord _
  · simp only [h, dif_neg, not_false_eq_true]
    exact differentiable_const _

theorem diff_cpt (X : Data E r) (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) := by
  refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
  show Differentiable ℂ fun z => (mat x0 τ * mat (nmat X z) τ) a b
  simp only [Matrix.mul_apply]
  exact Differentiable.fun_sum fun c _ => (diff_nmat X τ c b).const_mul _

theorem cont_nmatm (X : Data E r) (τ : X.Ψ) : Continuous fun w : V (nd X) => mat (nmat X w) τ := by
  refine continuous_pi fun a => continuous_pi fun b => ?_
  exact (diff_nmat X τ a b).continuous

def Jd (X : Data E r) : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)

def Gw (X : Data E r) (w : V (nd X)) (τ : X.Ψ) : Matrix (Fin r) (Fin r) ℂ :=
  (mat (nmat X w) τ)ᵀ * Jd X * (mat (nmat X w) τ).map (starRingEnd ℂ)

theorem dmin_cpt_orth (X : Data E r) {x : Frame X.Ψ r} (hx : IsOrth X x) (w : V (nd X)) (τ : X.Ψ)
    (i : Fin (r + 1)) : dmin X.Gm (cpt X x w) τ i = lminor (Gw X w τ) i := by
  unfold dmin
  show lminor (gram τ.1 X.Gm (mat x τ * mat (nmat X w) τ)) i = _
  rw [FrameDegreeData.gram_mul, hx τ]
  rfl

theorem cont_Gw (X : Data E r) (τ : X.Ψ) : Continuous fun w : V (nd X) => Gw X w τ := by
  unfold Gw
  exact ((cont_nmatm X τ).matrix_transpose.matrix_mul continuous_const).matrix_mul
    ((cont_nmatm X τ).matrix_map Complex.continuous_conj)

theorem cont_lminor (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) :
    Continuous fun w : V (nd X) => lminor (Gw X w τ) i := by
  unfold lminor
  exact ((cont_Gw X τ).matrix_submatrix _ _).matrix_det

theorem nmat_zero (X : Data E r) (τ : X.Ψ) : mat (nmat X 0) τ = 1 := by
  ext a b
  simp only [mat, nmat, Matrix.of_apply, Matrix.one_apply]
  by_cases h : b < a
  · rw [dif_pos h, if_neg (ne_of_gt h)]
    rfl
  · rw [dif_neg h]

theorem cpt_zero (X : Data E r) (x : Frame X.Ψ r) : cpt X x 0 = x := by
  funext τ
  show (mat x τ * mat (nmat X 0) τ : Matrix (Fin r) (Fin r) ℂ) = x τ
  rw [nmat_zero, Matrix.mul_one]
  rfl

theorem Gw_zero (X : Data E r) (τ : X.Ψ) : Gw X 0 τ = Jd X := by
  rw [Gw, nmat_zero]
  simp

theorem sgn_ne (p0 a : ℕ) : sgn p0 a ≠ 0 := by
  unfold sgn
  split_ifs <;> norm_num

theorem abs_sgn (p0 a : ℕ) : |sgn p0 a| = 1 := by
  unfold sgn
  split_ifs <;> simp

theorem lminor_Jd (X : Data E r) (i : Fin (r + 1)) : lminor (Jd X) i = ((psgn X.p0 i : ℝ) : ℂ) := by
  unfold lminor Jd psgn
  rw [Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _), Matrix.det_diagonal]
  simp only [Function.comp_apply, Fin.coe_castLE]
  push_cast
  exact Fin.prod_univ_eq_prod_range (fun a => ((sgn X.p0 a : ℝ) : ℂ)) i

theorem psgn_ne (p0 i : ℕ) : psgn p0 i ≠ 0 := by
  unfold psgn
  exact Finset.prod_ne_zero_iff.2 fun a _ => sgn_ne _ _

theorem abs_psgn (p0 i : ℕ) : |psgn p0 i| = 1 := by
  unfold psgn
  rw [Finset.abs_prod]
  exact Finset.prod_eq_one fun a _ => abs_sgn _ _

def nfw (X : Data E r) (la : Wt X.Ψ r) (w : V (nd X)) : ℝ :=
  ∏ τ, ∏ i : Fin r, ‖lminor (Gw X w τ) i.succ / lminor (Gw X w τ) i.castSucc‖ ^ (-(la τ i : ℝ) / 2)

theorem nfac_cpt_orth (X : Data E r) (la : Wt X.Ψ r) {x : Frame X.Ψ r} (hx : IsOrth X x)
    (w : V (nd X)) : X.nfac la (cpt X x w) = nfw X la w := by
  unfold Data.nfac nfw
  simp only [dmin_cpt_orth X hx w]

theorem norm_lminor_zero (X : Data E r) (τ : X.Ψ) (i : Fin (r + 1)) : ‖lminor (Gw X 0 τ) i‖ = 1 := by
  rw [Gw_zero, lminor_Jd, Complex.norm_real, Real.norm_eq_abs, abs_psgn]

theorem nfw_zero (X : Data E r) (la : Wt X.Ψ r) : nfw X la 0 = 1 := by
  unfold nfw
  simp only [norm_div, norm_lminor_zero, div_one, Real.one_rpow, Finset.prod_const_one]

theorem nfw_contAt (X : Data E r) (la : Wt X.Ψ r) : ContinuousAt (nfw X la) 0 := by
  unfold nfw
  refine tendsto_finset_prod _ fun τ _ => tendsto_finset_prod _ fun i _ => ?_
  have h1 : ContinuousAt (fun w => lminor (Gw X w τ) i.succ / lminor (Gw X w τ) i.castSucc) 0 :=
    ((cont_lminor X τ i.succ).continuousAt).div ((cont_lminor X τ i.castSucc).continuousAt)
      (by rw [← norm_ne_zero_iff, norm_lminor_zero]; exact one_ne_zero)
  exact h1.norm.rpow_const (Or.inl (by simp only [norm_div, norm_lminor_zero, div_one]; exact one_ne_zero))

theorem exp_neg_phla (X : Data E r) (la : Wt X.Ψ r) {y : Frame X.Ψ r} (h : 0 < X.nfac la y) :
    Real.exp (-phla X la y) = X.nfac la y ^ 2 := by
  unfold phla
  rw [neg_mul, neg_neg, mul_comm, Real.exp_mul, Real.exp_log h, Real.rpow_two]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Filter
open scoped ENNReal Matrix ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem cpt_mem_dom (X : Data E r) {x : Frame X.Ψ r} (hx : x ∈ X.dom) (hxo : IsOrth X x) {w : V (nd X)}
    (h1 : ∀ τ, (mat (nmat X w) τ).det ≠ 0)
    (h2 : ∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) :
    cpt X x w ∈ X.dom := fun τ =>
  ⟨by
    show (mat x τ * mat (nmat X w) τ).det ≠ 0
    rw [Matrix.det_mul]; exact mul_ne_zero (hx τ).1 (h1 τ),
   fun i => by rw [dmin_cpt_orth X hxo]; exact h2 τ i⟩

theorem good_ball (X : Data E r) (la : Wt X.Ψ r) : ∃ R > 0, ∀ w ∈ Metric.ball (0 : V (nd X)) R,
    (∀ τ, (mat (nmat X w) τ).det ≠ 0) ∧
      (∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) ∧ 1 / 2 < nfw X la w := by
  have hdet : ∀ τ, ∀ᶠ w in 𝓝 (0 : V (nd X)), (mat (nmat X w) τ).det ≠ 0 := fun τ => by
    have hc : ContinuousAt (fun w : V (nd X) => (mat (nmat X w) τ).det) 0 :=
      (cont_nmatm X τ).matrix_det.continuousAt
    have h0 : (mat (nmat X 0) τ).det ≠ 0 := by
      rw [nmat_zero, Matrix.det_one]
      exact one_ne_zero
    exact hc.eventually_ne h0
  have hmin : ∀ τ, ∀ i : Fin (r + 1), ∀ᶠ w in 𝓝 (0 : V (nd X)),
      0 < psgn X.p0 i * (lminor (Gw X w τ) i).re := fun τ i => by
    have hc : ContinuousAt (fun w => psgn X.p0 i * (lminor (Gw X w τ) i).re) 0 :=
      (continuous_const.mul (Complex.continuous_re.comp (cont_lminor X τ i))).continuousAt
    have h0 : 0 < psgn X.p0 i * (lminor (Gw X 0 τ) i).re := by
      rw [Gw_zero, lminor_Jd, Complex.ofReal_re]
      exact mul_self_pos.2 (psgn_ne _ _)
    exact hc.eventually (lt_mem_nhds h0)
  have hnf : ∀ᶠ w in 𝓝 (0 : V (nd X)), 1 / 2 < nfw X la w :=
    (nfw_contAt X la).eventually (lt_mem_nhds (by rw [nfw_zero]; norm_num))
  have hall : ∀ᶠ w in 𝓝 (0 : V (nd X)), (∀ τ, (mat (nmat X w) τ).det ≠ 0) ∧
      (∀ τ, ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (lminor (Gw X w τ) i).re) ∧ 1 / 2 < nfw X la w :=
    (Filter.eventually_all.2 hdet).and
      ((Filter.eventually_all.2 fun τ => Filter.eventually_all.2 (hmin τ)).and hnf)
  obtain ⟨R, hR, hball⟩ := Metric.eventually_nhds_iff_ball.1 hall
  exact ⟨R, hR, hball⟩

theorem subMean_holds : SubMeanStatement (E := E) := by
  intro r X la ρ hρ hρ1
  obtain ⟨R0, hR0, hgood⟩ := good_ball X la
  set R := min R0 ρ with hR
  have hR0' : 0 < R := lt_min hR0 hρ
  have hvpos : volume (Metric.ball (0 : V (nd X)) R) ≠ 0 := (Metric.measure_ball_pos volume _ hR0').ne'
  have hvtop : volume (Metric.ball (0 : V (nd X)) R) ≠ ⊤ := measure_ball_lt_top.ne
  refine ⟨(volume (Metric.ball (0 : V (nd X)) R))⁻¹ * ENNReal.ofReal 4,
    ENNReal.mul_lt_top (ENNReal.inv_lt_top.2 (pos_iff_ne_zero.2 hvpos)) ENNReal.ofReal_lt_top,
    fun P hP x hx hxo => ?_⟩
  have hgoodR := fun w (hw : w ∈ Metric.ball (0 : V (nd X)) R) =>
    hgood w (Metric.ball_subset_ball (min_le_left _ _) hw)
  have hmem : Metric.ball (0 : V (nd X)) R ⊆ Bset X x ρ := fun w hw => by
    obtain ⟨h1, h2, -⟩ := hgoodR w hw
    exact ⟨lt_of_lt_of_le (mem_ball_zero_iff.1 hw) (min_le_right _ _), cpt_mem_dom X hx hxo h1 h2⟩
  have hu : DifferentiableOn ℂ (fun w => P (cpt X x w)) (Metric.ball 0 R) :=
    hP.comp (diff_cpt X x).differentiableOn fun w hw => (hmem hw).2
  have hmv := ReciprocityTheory.L2DbarEstimates.C.mv (nd X) 0 R (fun w => P (cpt X x w)) (fun _ => 1) hu measurable_const
  simp only [mul_one, one_mul, lintegral_const, Measure.restrict_apply_univ, cpt_zero] at hmv
  have hpt : ∀ w ∈ Metric.ball (0 : V (nd X)) R, ‖P (cpt X x w)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
      (‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by
    intro w hw
    obtain ⟨-, -, h3⟩ := hgoodR w hw
    have hn : X.nfac la (cpt X x w) = nfw X la w := nfac_cpt_orth X la hxo w
    have he : 1 ≤ ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
      rw [exp_neg_phla X la (by rw [hn]; linarith), hn, ← ENNReal.ofReal_mul (by norm_num),
        ← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (by nlinarith)
    calc ‖P (cpt X x w)‖ₑ ^ 2 = ‖P (cpt X x w)‖ₑ ^ 2 * 1 := (mul_one _).symm
      _ ≤ ‖P (cpt X x w)‖ₑ ^ 2 *
          (ENNReal.ofReal 4 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) := by gcongr
      _ = _ := by ring
  have hint : ∫⁻ z in Metric.ball (0 : V (nd X)) R, ‖P (cpt X x z)‖ₑ ^ 2 ≤ ENNReal.ofReal 4 *
      ∫⁻ w in Bset X x ρ, ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w))) := by
    calc ∫⁻ z in Metric.ball (0 : V (nd X)) R, ‖P (cpt X x z)‖ₑ ^ 2
        ≤ ∫⁻ z in Metric.ball (0 : V (nd X)) R, ENNReal.ofReal 4 *
            (‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z)))) :=
          setLIntegral_mono' Metric.isOpen_ball.measurableSet hpt
      _ = ENNReal.ofReal 4 * ∫⁻ z in Metric.ball (0 : V (nd X)) R,
            ‖P (cpt X x z)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x z))) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul_of_nonneg_left (lintegral_mono_set hmem) zero_le
  have hle : ‖P x‖ₑ ^ 2 ≤ (volume (Metric.ball (0 : V (nd X)) R))⁻¹ *
      ∫⁻ z in Metric.ball (0 : V (nd X)) R, ‖P (cpt X x z)‖ₑ ^ 2 := by
    rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl hvpos) (Or.inl hvtop)]
    exact hmv
  calc ‖P x‖ₑ ^ 2 ≤ (volume (Metric.ball (0 : V (nd X)) R))⁻¹ * (ENNReal.ofReal 4 *
        ∫⁻ w in Bset X x ρ, ‖P (cpt X x w)‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-phla X la (cpt X x w)))) :=
        hle.trans (mul_le_mul_of_nonneg_left hint zero_le)
    _ = _ := by ring

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.PoinPf
