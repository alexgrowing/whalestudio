import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfS

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem chi_norm (la : Wt X.Ψ r) {γ : GL (Fin r) E} (hγ : γ ∈ X.Γ) : ‖X.χ la γ‖ = 1 := by
  obtain ⟨n, hn, h⟩ := X.χ_fin la
  have h1 := congrArg norm (h γ hγ)
  rw [norm_pow, norm_one] at h1
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').mp h1

theorem bchar_ne (la : Wt X.Ψ r) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r) : bchar la b ≠ 0 := by
  have hb' : ∀ τ : X.Ψ, (mat b τ).det ≠ 0 ∧ ∀ a c : Fin r, c < a → b τ a c = 0 := hb
  unfold bchar
  rw [Finset.prod_ne_zero_iff]
  intro τ _
  rw [Finset.prod_ne_zero_iff]
  intro i _
  have hd := (hb' τ).1
  have hbt : (mat b τ).BlockTriangular id := fun a c hca => (hb' τ).2 a c hca
  rw [Matrix.det_of_upperTriangular hbt, Finset.prod_ne_zero_iff] at hd
  have hi := hd i (Finset.mem_univ _)
  exact zpow_ne_zero _ hi

open Classical in

def phiF (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) : Frame X.Ψ r → ℝ≥0∞ :=
  fun y => X.dom.piecewise (fun y => ENNReal.ofReal (‖f0 y‖ ^ 2)) 0 y * W y

theorem phiF_dom (f0 : Frame X.Ψ r → ℂ) (W : Frame X.Ψ r → ℝ≥0∞) {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    phiF X f0 W x = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by
  simp [phiF, Set.piecewise, hx]

theorem phiF_meas {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞} (hf : ContinuousOn f0 X.dom)
    (hW : Measurable W) : Measurable (phiF X f0 W) := by
  classical
  have hopen : IsOpen X.dom := by
    have h1 : X.dom = ⋂ τ : X.Ψ, ({x : Frame X.Ψ r | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_setOf_eq]
      rfl
    rw [h1]
    refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
    · refine isOpen_ne_fun ?_ continuous_const
      unfold mat
      fun_prop
    · refine isOpen_lt continuous_const ?_
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
  unfold phiF
  refine Measurable.mul ?_ hW
  refine ContinuousOn.measurable_piecewise ?_ continuousOn_const hopen.measurableSet
  exact ENNReal.continuous_ofReal.comp_continuousOn (hf.norm.pow 2)

theorem phiF_B {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf0 : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, f0 (rmul x b) = bchar la b * f0 x)
    (hW : IsMetricW X la W) : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, phiF X f0 W (rmul x b) = phiF X f0 W x := by
  intro x hx b hb
  rw [phiF_dom X f0 W (dom_rmul X hx hb), phiF_dom X f0 W hx, hf0 x hx b hb, hW.2.1 x hx b hb,
    norm_mul, mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
  have hA0 : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact pow_pos (norm_pos_iff.2 (bchar_ne X la hb)) 2
  have hAt : ENNReal.ofReal (‖bchar la b‖ ^ 2) ≠ ⊤ := ENNReal.ofReal_ne_top
  rw [ENNReal.div_eq_inv_mul]
  calc ENNReal.ofReal (‖bchar la b‖ ^ 2) * ENNReal.ofReal (‖f0 x‖ ^ 2) *
        ((ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹ * W x)
      = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x *
          (ENNReal.ofReal (‖bchar la b‖ ^ 2) * (ENNReal.ofReal (‖bchar la b‖ ^ 2))⁻¹) := by ring
    _ = ENNReal.ofReal (‖f0 x‖ ^ 2) * W x := by rw [ENNReal.mul_inv_cancel hA0 hAt, mul_one]

theorem phiF_G {la : Wt X.Ψ r} {f0 : Frame X.Ψ r → ℂ} {W : Frame X.Ψ r → ℝ≥0∞}
    (hf0 : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, f0 (lact γ x) = X.χ la γ * f0 x)
    (hW : IsMetricW X la W) : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, phiF X f0 W (lact γ x) = phiF X f0 W x := by
  intro γ hγ x hx
  rw [phiF_dom X f0 W (dom_lact X hγ hx), phiF_dom X f0 W hx, hf0 γ hγ x hx, hW.2.2 γ hγ x hx,
    norm_mul, chi_norm X la hγ, one_mul]

variable (x0 : Frame X.Ψ r)

theorem nfac_pos {la : Wt X.Ψ r} {z : V (nd X)} (hz : z ∈ OmF X x0) : 0 < X.nfac la (cpt X x0 z) := by
  have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
      ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
  have hd : ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro τ i h
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply Finset.prod_pos
  intro τ _
  apply Finset.prod_pos
  intro i _
  exact Real.rpow_pos_of_pos (norm_pos_iff.mpr (div_ne_zero (hd τ _) (hd τ _))) _

theorem nfac_cont (la : Wt X.Ψ r) : ContinuousOn (fun z => X.nfac la (cpt X x0 z)) (OmF X x0) := by
  have hn : Continuous fun z : V (nd X) => nmat X z := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    unfold nmat
    by_cases h : b < a
    · simp only [h, dif_pos]
      fun_prop
    · simp only [h, dif_neg, not_false_eq_true]
      exact continuous_const
  have hc : Continuous fun z : V (nd X) => cpt X x0 z := by
    refine continuous_pi fun τ => ?_
    show Continuous fun z : V (nd X) => mat x0 τ * mat (nmat X z) τ
    exact continuous_const.matrix_mul ((continuous_apply τ).comp hn)
  have hd : ∀ τ i, Continuous fun z : V (nd X) => dmin X.Gm (cpt X x0 z) τ i := by
    intro τ i
    have h1 : Continuous fun x : Frame X.Ψ r => dmin X.Gm x τ i := by
      unfold dmin lminor ReciprocityTheory.ChartRestriction.G.FD.gram ReciprocityTheory.ChartRestriction.G.FD.hermC ReciprocityTheory.ChartRestriction.G.FD.col mat
      fun_prop
    exact h1.comp hc
  have hne : ∀ z ∈ OmF X x0, ∀ τ i, dmin X.Gm (cpt X x0 z) τ i ≠ 0 := by
    intro z hz τ i h
    have hz' : ∀ τ : X.Ψ, (mat (cpt X x0 z) τ).det ≠ 0 ∧
        ∀ i : Fin (r + 1), 0 < psgn X.p0 i * (dmin X.Gm (cpt X x0 z) τ i).re := hz
    have h2 := (hz' τ).2 i
    rw [h, Complex.zero_re, mul_zero] at h2
    exact lt_irrefl _ h2
  unfold ReciprocityTheory.ChartRestriction.G.FD.Data.nfac
  apply continuousOn_finset_prod
  intro τ _
  apply continuousOn_finset_prod
  intro i _
  intro z hz
  apply ContinuousAt.continuousWithinAt
  apply ContinuousAt.rpow_const
  · exact ((hd τ _).continuousAt.div (hd τ _).continuousAt (hne z hz τ _)).norm
  · left
    exact norm_ne_zero_iff.mpr (div_ne_zero (hne z hz τ _) (hne z hz τ _))

theorem expPhla_cont (la : Wt X.Ψ r) :
    ContinuousOn (fun z => Real.exp (-phla X la (cpt X x0 z))) (OmF X x0) := by
  unfold phla
  have h1 := nfac_cont X x0 la
  exact (continuousOn_const.mul (h1.log fun z hz => (nfac_pos X x0 (la := la) hz).ne')).neg.rexp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoE
