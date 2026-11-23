import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfD

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExF

open NumberField Complex Matrix Topology Filter ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst
  ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.ExhA ReciprocityTheory.ChartRestriction.G.AR.Up.ExhB
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExhC ReciprocityTheory.ChartRestriction.G.AR.Up.ExhD ReciprocityTheory.ChartRestriction.G.AR.Up.ExhE
open scoped ComplexConjugate ComplexOrder ContDiff

noncomputable section

theorem levi_logNormSq_zero {n : ℕ} (h : V n → ℂ) (hh : ContDiff ℂ ∞ h) (v0 : V n)
    (hne : h v0 ≠ 0) (ξ : Fin n → ℂ) :
    leviV n (fun y => ((Real.log (Complex.normSq (h y)) : ℝ) : ℂ)) v0 ξ = 0 := by
  have hl := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n 1 (fun _ => h) v0 ξ
    (fun _ => hh.contDiffAt.of_le two_le_infty) (by intro h'; exact hne (congrFun h' 0))
  have e1 : (fun y => ((Real.log (sqNorm (fun i : Fin 1 => (fun _ => h) i y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (Complex.normSq (h y)) : ℝ) : ℂ) := by
    funext y; simp [sqNorm]
  rw [e1] at hl
  rw [hl]
  have hn : (Complex.normSq (h v0) : ℂ) ≠ 0 := by
    exact_mod_cast (Complex.normSq_pos.2 hne).ne'
  have hP : projPerp (fun _ : Fin 1 => h v0) = 0 := by
    ext i l
    fin_cases i; fin_cases l
    simp [projPerp, sqNorm, vecMulVec_apply, Complex.mul_conj, hn]
  simp [hP, sqNorm]

theorem leviT_nonneg {n : ℕ} (v0 : V n) (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ)) v0 ξ).re := by
  let g : Fin (n + 1) → V n → ℂ := fun i =>
    Fin.cons (α := fun _ => V n → ℂ) (fun _ : V n => (1 : ℂ)) (fun j : Fin n => fun y : V n => y j) i
  have hc : ∀ i, ContDiffAt ℂ 2 (g i) v0 := by
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [g, Fin.cons_zero]; exact contDiffAt_const
    · simp only [g, Fin.cons_succ]; exact (cd_coord _).contDiffAt.of_le two_le_infty
  have hne : (fun i => g i v0) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp [g] at this
  have h := ReciprocityTheory.L2DbarEstimates.H.leviLogNormSq n (n + 1) g v0 ξ hc hne
  have e1 : (fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (1 + ‖y‖ ^ 2) : ℝ) : ℂ) := by
    funext y
    simp [sqNorm, Fin.sum_univ_succ, g, EuclideanSpace.norm_sq_eq, Complex.normSq_eq_norm_sq]
  rw [e1] at h
  rw [h, Complex.ofReal_re]
  exact div_nonneg (sqNorm_nonneg' _) (sqNorm_nonneg' _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem rhF_eq_log (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {y : V (nd X)} (hy : y ∈ OmF X x0) :
    rhF X x0 y = -Real.log (∏ τ, (Am X y τ).det.re) := by
  have key : ∀ τ, 0 < (Am X y τ).det.re ∧ ‖(Am X y τ).det‖ = (Am X y τ).det.re := by
    intro τ
    have hpos := ((mem_OmF_iff X x0 ho y).1 hy τ).det_pos
    have h := Complex.lt_def.1 hpos
    simp only [Complex.zero_re, Complex.zero_im] at h
    refine ⟨h.1, ?_⟩
    rw [show (Am X y τ).det = ((Am X y τ).det.re : ℂ) from Complex.ext (by simp) (by simp [← h.2])]
    rw [Complex.norm_real, Complex.ofReal_re, Real.norm_of_nonneg h.1.le]
  rw [rhF_eq_sum X x0 ho y, Real.log_prod (fun τ _ => (key τ).1.ne')]
  congr 1
  exact Finset.sum_congr rfl fun τ _ => by rw [(key τ).2]

theorem levi_rhF_nonneg (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z0 : V (nd X)} (hz0 : z0 ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    0 ≤ (leviV (nd X) (fun y => ((rhF X x0 y : ℝ) : ℂ)) z0 ξ).re := by
  set Hf : V (nd X) → ℂ := fun y => ∏ τ, (1 - Zt X y τ * (Zt X z0 τ)ᴴ).det with hHf
  have hHcd : ContDiff ℂ ∞ Hf := by
    refine contDiff_prod fun τ _ => contDiff_det_of fun a b => ?_
    simp only [Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
    exact contDiff_const.sub (ContDiff.sum fun c _ => (cd_Zt X τ a c).mul contDiff_const)
  set P : V (nd X) → ℝ := fun y => ∏ τ, (Am X y τ).det.re with hP
  have hAm : ∀ y ∈ OmF X x0, ∀ τ, (Am X y τ).PosDef := fun y hy => (mem_OmF_iff X x0 ho y).1 hy
  have hPpos : ∀ y ∈ OmF X x0, 0 < P y := fun y hy =>
    Finset.prod_pos fun τ _ => (det_re_pos_im (hAm y hy τ)).1
  have hle : ∀ y ∈ OmF X x0, P y * P z0 ≤ Complex.normSq (Hf y) := by
    intro y hy
    simp only [hP, hHf]
    rw [← Finset.prod_mul_distrib, map_prod]
    exact Finset.prod_le_prod (fun τ _ => mul_nonneg (det_re_pos_im (hAm y hy τ)).1.le
      (det_re_pos_im (hAm z0 hz0 τ)).1.le)
      (fun τ _ => det_mul_det_le_normSq_det _ _ (hAm y hy τ) (hAm z0 hz0 τ))
  have hself : Complex.normSq (Hf z0) = P z0 * P z0 := by
    simp only [hP, hHf]
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    have e : (1 - Zt X z0 τ * (Zt X z0 τ)ᴴ) = Am X z0 τ := rfl
    rw [e, det_eq_ofReal (hAm z0 hz0 τ), Complex.normSq_ofReal]
    simp
  set F : V (nd X) → ℝ := fun y => rhF X x0 y + Real.log (Complex.normSq (Hf y)) with hF
  have hmin : ∀ y ∈ OmF X x0, F z0 ≤ F y := by
    intro y hy
    have h2 := Real.log_le_log (mul_pos (hPpos y hy) (hPpos z0 hz0)) (hle y hy)
    rw [Real.log_mul (hPpos y hy).ne' (hPpos z0 hz0).ne'] at h2
    have h3 : F z0 = Real.log (P z0) := by
      simp only [hF]
      rw [hself, rhF_eq_log X x0 ho hz0, Real.log_mul (hPpos z0 hz0).ne' (hPpos z0 hz0).ne']
      ring
    rw [h3]
    simp only [hF]
    rw [rhF_eq_log X x0 ho hy]
    linarith
  have hmax : IsLocalMax (fun y => -F y) z0 := by
    have : IsLocalMin F z0 :=
      Filter.eventually_of_mem ((isOpen_OmF X x0).mem_nhds hz0) fun y hy => hmin y hy
    exact this.neg
  have hNpos : Complex.normSq (Hf z0) ≠ 0 := by
    rw [hself]; have := hPpos z0 hz0; positivity
  have hHne : Hf z0 ≠ 0 := fun h => hNpos (by rw [h]; simp)
  have hc1 : ContDiffAt ℝ 2 (fun y => rhF X x0 y) z0 := (rhF_contDiffAt X x0 ho hz0).of_le two_le_infty
  have hc2 : ContDiffAt ℝ 2 (fun y => Real.log (Complex.normSq (Hf y))) z0 := by
    have hn : ContDiff ℝ ∞ fun y : V (nd X) => Complex.normSq (Hf y) := by
      simp only [Complex.normSq_eq_norm_sq]
      exact (contDiff_norm_sq ℝ).comp (hHcd.restrict_scalars ℝ)
    exact ((Real.contDiffAt_log.2 hNpos).comp z0 hn.contDiffAt).of_le two_le_infty
  have hcF : ContDiffAt ℝ 2 F z0 := hc1.add hc2
  have h1 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_re_nonpos_of_isLocalMax hcF.neg hmax ξ
  have e1 : (fun y => ((-F y : ℝ) : ℂ)) = fun y => (((-1) * F y : ℝ) : ℂ) := by
    funext y; simp
  rw [e1, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-1) hcF ξ] at h1
  have e2 : (fun y => ((F y : ℝ) : ℂ)) =
      fun y => ((rhF X x0 y + Real.log (Complex.normSq (Hf y)) : ℝ) : ℂ) := rfl
  rw [e2, ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add hc1 hc2 ξ,
    levi_logNormSq_zero Hf hHcd z0 hHne ξ] at h1
  simp at h1
  linarith

private theorem det_one_sub_mul_conjTranspose_mem_Icc {p q : ℕ} (Z : Matrix (Fin p) (Fin q) ℂ) (h : (1 - Z * Zᴴ).PosSemidef) :
    0 ≤ (1 - Z * Zᴴ).det.re ∧ (1 - Z * Zᴴ).det.re ≤ 1 ∧ ‖(1 - Z * Zᴴ).det‖ = (1 - Z * Zᴴ).det.re := by
  have hH : (1 - Z * Zᴴ).IsHermitian := h.isHermitian
  have hev : ∀ i, 0 ≤ hH.eigenvalues i ∧ hH.eigenvalues i ≤ 1 := by
    intro i
    refine ⟨h.eigenvalues_nonneg i, ?_⟩
    rw [hH.eigenvalues_eq i]
    set v := (hH.eigenvectorBasis i).ofLp with hvdef
    have hv : star v ⬝ᵥ v = 1 := by
      have h1 : ‖hH.eigenvectorBasis i‖ = 1 := hH.eigenvectorBasis.orthonormal.1 i
      rw [EuclideanSpace.norm_eq, Real.sqrt_eq_one] at h1
      simp only [dotProduct, Pi.star_apply, RCLike.star_def, RCLike.conj_mul]
      rw [hvdef]
      have h2 := congrArg (fun t : ℝ => (t : ℂ)) h1
      push_cast at h2
      exact h2
    have hq : 0 ≤ star v ⬝ᵥ (Z * Zᴴ) *ᵥ v := (posSemidef_self_mul_conjTranspose Z).dotProduct_mulVec_nonneg v
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hv, map_sub, RCLike.one_re]
    have := (RCLike.nonneg_iff.1 hq).1
    linarith
  have hd : (1 - Z * Zᴴ).det = ((∏ i, hH.eigenvalues i : ℝ) : ℂ) := by
    rw [hH.det_eq_prod_eigenvalues]
    push_cast
    rfl
  have h0 : 0 ≤ ∏ i, hH.eigenvalues i := Finset.prod_nonneg fun i _ => (hev i).1
  rw [hd, Complex.ofReal_re, Complex.norm_real, Real.norm_of_nonneg h0]
  exact ⟨h0, Finset.prod_le_one (fun i _ => (hev i).1) fun i _ => (hev i).2, rfl⟩

theorem rhF_nonneg (x0 : Frame X.Ψ r) (ho : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 ≤ rhF X x0 z := by
  rw [rhF_eq_sum X x0 ho z, neg_nonneg]
  refine Finset.sum_nonpos fun τ _ => Real.log_nonpos (norm_nonneg _) ?_
  obtain ⟨h0, h1, h2⟩ : 0 ≤ (Am X z τ).det.re ∧ (Am X z τ).det.re ≤ 1 ∧ ‖(Am X z τ).det‖ = (Am X z τ).det.re :=
    det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) ((mem_OmF_iff X x0 ho z).1 hz τ).posSemidef
  rw [h2]
  exact h1

theorem sub_eqF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (a : ℝ) :
    {z : V (nd X) | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} =
      {z | (∀ τ, (Am X z τ).PosSemidef) ∧
        Real.exp (Real.log (1 + ‖z‖ ^ 2) - a) ≤ ∏ τ, (Am X z τ).det.re} := by
  ext z
  simp only [Set.mem_setOf_eq]
  constructor
  · rintro ⟨hz, hle⟩
    have hpd := (mem_OmF_iff X x0 ho z).1 hz
    refine ⟨fun τ => (hpd τ).posSemidef, ?_⟩
    have hpos : ∀ τ, 0 < (Am X z τ).det.re := fun τ => by
      have h := Complex.lt_def.1 (hpd τ).det_pos
      simp only [Complex.zero_re] at h
      exact h.1
    unfold eF at hle
    rw [rhF_eq_log X x0 ho hz] at hle
    have hP : 0 < ∏ τ, (Am X z τ).det.re := Finset.prod_pos fun τ _ => hpos τ
    rw [← Real.exp_log hP]
    exact Real.exp_le_exp.2 (by linarith)
  · rintro ⟨hpsd, hle⟩
    have hP : 0 < ∏ τ, (Am X z τ).det.re := lt_of_lt_of_le (Real.exp_pos _) hle
    have hpos : ∀ τ, 0 < (Am X z τ).det.re := by
      intro τ
      obtain ⟨h0, -, -⟩ : 0 ≤ (Am X z τ).det.re ∧ (Am X z τ).det.re ≤ 1 ∧
          ‖(Am X z τ).det‖ = (Am X z τ).det.re := det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) (hpsd τ)
      rcases h0.eq_or_lt with h0 | h0
      · exact absurd hP (by rw [Finset.prod_eq_zero (Finset.mem_univ τ) h0.symm]; exact lt_irrefl 0)
      · exact h0
    have hz : z ∈ OmF X x0 := (mem_OmF_iff X x0 ho z).2 fun τ => ((hpsd τ).posDef_iff_isUnit).2
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h => by
        have := hpos τ
        rw [h, Complex.zero_re] at this
        exact lt_irrefl 0 this))
    refine ⟨hz, ?_⟩
    unfold eF
    rw [rhF_eq_log X x0 ho hz]
    have := Real.log_le_log (Real.exp_pos _) hle
    rw [Real.log_exp] at this
    linarith

theorem isClosed_psdF : IsClosed {z : V (nd X) | ∀ τ, (Am X z τ).PosSemidef} := by
  have hset : {z : V (nd X) | ∀ τ, (Am X z τ).PosSemidef} =
      ⋂ τ, ⋂ x : Fin X.p0 → ℂ, {z | 0 ≤ star x ⬝ᵥ (Am X z τ) *ᵥ x} := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    refine ⟨fun h τ x => (h τ).dotProduct_mulVec_nonneg x, fun h τ => ?_⟩
    exact Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      (Matrix.isHermitian_one.sub (Matrix.isHermitian_mul_conjTranspose_self _)) (h τ)
  rw [hset]
  refine isClosed_iInter fun τ => isClosed_iInter fun x => ?_
  have he : ∀ a c, Continuous fun z : V (nd X) => Am X z τ a c := fun a c => (cd_Am_entry X τ a c).continuous
  have hf : Continuous fun z : V (nd X) => star x ⬝ᵥ (Am X z τ) *ᵥ x := by
    simp only [dotProduct, Matrix.mulVec]
    exact continuous_finset_sum _ fun a _ =>
      continuous_const.mul (continuous_finset_sum _ fun c _ => (he a c).mul continuous_const)
  exact isClosed_le continuous_const hf

theorem isCompact_subF (x0 : Frame X.Ψ r) (ho : IsOrth X x0) (a : ℝ) : IsCompact {z : V (nd X) | z ∈ OmF X x0 ∧ eF X x0 z ≤ a} := by
  rw [sub_eqF X x0 ho a, Set.setOf_and]
  apply Metric.isCompact_of_isClosed_isBounded
  · refine (isClosed_psdF X).inter (isClosed_le ?_ ?_)
    · exact Real.continuous_exp.comp ((Continuous.log (continuous_const.add (continuous_norm.pow 2))
        fun z => (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2).ne').sub continuous_const)
    · exact continuous_finset_prod _ fun τ _ => Complex.continuous_re.comp (cd_detAm X τ).continuous
  · refine (Metric.isBounded_iff_subset_closedBall 0).2 ⟨Real.exp a, fun z hz => ?_⟩
    obtain ⟨hpsd, hle⟩ := hz
    have hP : ∏ τ, (Am X z τ).det.re ≤ 1 :=
      Finset.prod_le_one (fun τ _ => (det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) (hpsd τ)).1)
        fun τ _ => (det_one_sub_mul_conjTranspose_mem_Icc (Zt X z τ) (hpsd τ)).2.1
    have h1 : Real.log (1 + ‖z‖ ^ 2) - a ≤ 0 := Real.exp_le_one_iff.1 (le_trans hle hP)
    have h2 : 1 + ‖z‖ ^ 2 ≤ Real.exp a := by
      rw [← Real.exp_log (by positivity : (0 : ℝ) < 1 + ‖z‖ ^ 2)]
      exact Real.exp_le_exp.2 (by linarith)
    rw [Metric.mem_closedBall, dist_zero_right]
    nlinarith [sq_nonneg (‖z‖ - 1), norm_nonneg z]

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExF
