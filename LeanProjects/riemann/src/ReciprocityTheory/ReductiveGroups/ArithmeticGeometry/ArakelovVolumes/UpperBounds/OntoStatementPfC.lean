import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.HoloSmooth

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC

open NumberField Complex Matrix Topology Filter MeasureTheory Set ReciprocityTheory.ChartRestriction.G.FD
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up
  ReciprocityTheory.ChartRestriction.G.AR.Up.OntoA ReciprocityTheory.ChartRestriction.G.AR.Up.OntoB
open scoped ComplexConjugate ContDiff ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) (x0 : Frame X.Ψ r)

def Om1 (g1 : V (nd X) → ℂ) : Set (V (nd X)) := {z | z ∈ OmF X x0 ∧ g1 z ≠ 0}

theorem isOpen_nonvanishingLocus {g1 : V (nd X) → ℂ} (hg1 : DifferentiableOn ℂ g1 (OmF X x0)) :
    IsOpen (Om1 X x0 g1) :=
  hg1.continuousOn.isOpen_inter_preimage (isOpen_OmF (X := X) (x0 := x0)) isOpen_compl_singleton

theorem measurable_densF : Measurable fun z => ENNReal.ofReal (densF X x0 z) := by
  have hn : Continuous (nmat X) := by
    refine continuous_pi fun τ => continuous_pi fun a => continuous_pi fun b => ?_
    by_cases h : b < a
    · simp only [nmat, dif_pos h]
      fun_prop
    · by_cases h' : a = b
      · simp only [nmat, dif_neg h, if_pos h']
        exact continuous_const
      · simp only [nmat, dif_neg h, if_neg h']
        exact continuous_const
  have hc : ∀ τ i, Continuous fun z => dmin X.Gm (cpt X x0 z) τ i := by
    intro τ i
    simp only [dmin, lminor, ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mat, cpt, rmul]
    fun_prop
  refine ENNReal.measurable_ofReal.comp ?_
  unfold densF
  refine Finset.measurable_prod _ fun τ _ => Finset.measurable_prod _ fun i _ => ?_
  simp only [_root_.zpow_neg, _root_.zpow_two]
  exact ((hc τ i.castSucc).measurable.norm.mul (hc τ i.castSucc).measurable.norm).inv

theorem setLIntegral_muF {U : Set (V (nd X))} (hU : MeasurableSet U) (hUO : U ⊆ OmF X x0)
    (g : V (nd X) → ℝ≥0∞) :
    ∫⁻ z in U, g z ∂muF X x0 = ∫⁻ z in U, ENNReal.ofReal (densF X x0 z) * g z := by
  unfold muF
  rw [restrict_withDensity hU, lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (measurable_densF X x0) (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_restrict hU, Set.inter_eq_left.mpr hUO]
  rfl

theorem deriv_ka (bb t : ℝ) : deriv (fun t : ℝ => Real.exp (-bb * t)) t = -bb * Real.exp (-bb * t) := by
  have h : HasDerivAt (fun t : ℝ => Real.exp (-bb * t)) (Real.exp (-bb * t) * (-bb * 1)) t :=
    ((hasDerivAt_id t).const_mul (-bb)).exp
  rw [h.deriv]
  ring

private lemma wdb_holo_lemma {n : ℕ} (j : Fin n) {g : V n → ℂ} {y : V n}
    (hg : DifferentiableAt ℂ g y) : wdb n j g y = 0 := by
  unfold wdb
  rw [hg.fderiv_restrictScalars ℝ]
  have hI : ∀ A : ℂ, Complex.I * (Complex.I * A) = -A := fun A => by
    rw [← mul_assoc, Complex.I_mul_I]
    ring
  simp [hI]

theorem dbar_ka (bb : ℝ) {f0 : Frame X.Ψ r → ℂ} (hf0 : DifferentiableOn ℂ f0 X.dom) {y : V (nd X)}
    (hy : y ∈ OmF X x0) (ξ : Fin (nd X) → ℂ) :
    ∑ j, wdb (nd X) j (fun z => (kaF X x0 bb z : ℂ) * f0 (cpt X x0 z)) y * conj (ξ j) =
      ((-bb * kaF X x0 bb y : ℝ) : ℂ) * f0 (cpt X x0 y) *
        conj (∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) y * ξ j) := by
  have hn : ∀ τ a b, Differentiable ℂ fun z : V (nd X) => nmat X z τ a b := by
    intro τ a b
    by_cases h : b < a
    · simp only [nmat, dif_pos h]
      first
        | fun_prop
        | exact (EuclideanSpace.proj _).differentiable
    · by_cases h' : a = b
      · simp only [nmat, dif_neg h, if_pos h']
        exact differentiable_const _
      · simp only [nmat, dif_neg h, if_neg h']
        exact differentiable_const _
  have hcpt : Differentiable ℂ (cpt X x0) := by
    refine differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b => ?_
    simp only [cpt, rmul, mat, Matrix.mul_apply, Matrix.of_apply]
    exact Differentiable.fun_sum fun k _ => (hn τ k b).const_mul _
  have hF : DifferentiableAt ℂ (fun z => f0 (cpt X x0 z)) y :=
    ((hf0 (cpt X x0 y) hy).comp y (hcpt y).differentiableWithinAt (fun z hz => hz)).differentiableAt
      ((isOpen_OmF (X := X) (x0 := x0)).mem_nhds hy)
  have hcR : Differentiable ℝ (cpt X x0) := hcpt.restrictScalars ℝ
  have hdm : ∀ τ i, Differentiable ℝ fun z => dmin X.Gm (cpt X x0 z) τ i := by
    intro τ i
    simp only [dmin, lminor, ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, mat,
      Matrix.det_apply', Matrix.submatrix_apply, Matrix.of_apply, ← Complex.conjCLE_apply]
    fun_prop
  have hne : ∀ τ, dmin X.Gm (cpt X x0 y) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩ ≠ 0 := by
    intro τ h0
    have h1 := (hy τ).2 ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩
    rw [h0] at h1
    simp at h1
  have hrh : DifferentiableAt ℝ (rhF X x0) y := by
    have h2 : rhF X x0 = fun z =>
        -∑ τ, Real.log ‖dmin X.Gm (cpt X x0 z) τ ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩‖ := rfl
    rw [h2]
    refine (DifferentiableAt.fun_sum fun τ _ => ?_).neg
    exact (((hdm τ _).differentiableAt).norm ℂ (hne τ)).log (norm_ne_zero_iff.mpr (hne τ))
  have hR' : HasFDerivAt (rhF X x0) (fderiv ℝ (rhF X x0) y) y := hrh.hasFDerivAt
  have hK : HasFDerivAt (fun z => ((kaF X x0 bb z : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (Real.exp (-bb * rhF X x0 y) • ((-bb) • fderiv ℝ (rhF X x0) y))) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y ((hR'.const_mul (-bb)).exp)
  have hka : DifferentiableAt ℝ (kaF X x0 bb) y := ((hR'.const_mul (-bb)).exp).differentiableAt
  have hRc : HasFDerivAt (fun w => ((rhF X x0 w : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (fderiv ℝ (rhF X x0) y)) y :=
    Complex.ofRealCLM.hasFDerivAt.comp y hR'
  have hwd : ∀ j, wd (nd X) j (fun z => ((kaF X x0 bb z : ℝ) : ℂ)) y =
      ((-bb * kaF X x0 bb y : ℝ) : ℂ) * wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) y := by
    intro j
    unfold wd
    rw [hK.fderiv, hRc.fderiv]
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, kaF]
    push_cast
    ring
  have hw : ∀ j, wdb (nd X) j (fun z => (kaF X x0 bb z : ℂ) * f0 (cpt X x0 z)) y =
      ((-bb * kaF X x0 bb y : ℝ) : ℂ) * f0 (cpt X x0 y) *
        conj (wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) y) := by
    intro j
    rw [wdb_mul hK.differentiableAt (hF.restrictScalars ℝ), wdb_holo_lemma j hF, wdb_ofReal hka,
      hwd j, map_mul, Complex.conj_ofReal]
    ring
  simp only [hw, map_sum, map_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem ofReal_mul_ofReal_nonneg {a b : ℝ} (ha : 0 ≤ a) : ENNReal.ofReal a * ENNReal.ofReal b = ENNReal.ofReal (a * b) :=
  (ENNReal.ofReal_mul ha).symm

theorem exp_ph (Ps : V (nd X) → ℝ) (bb : ℝ) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    Real.exp (-((Ps z - Real.log (densF X x0 z)) + (-bb) * rhF X x0 z)) =
      Real.exp (-Ps z) * densF X x0 z / kaF X x0 bb z := by
  have hd := densF_pos (X := X) (x0 := x0) hz
  unfold kaF
  rw [show -((Ps z - Real.log (densF X x0 z)) + (-bb) * rhF X x0 z) =
      -Ps z + Real.log (densF X x0 z) - -bb * rhF X x0 z by ring,
    Real.exp_sub, Real.exp_add, Real.exp_log hd]

theorem horm_step (hExG : ExhaustGStatement (E := E)) (hGrad : RhGradFStatement (E := E)) (hx0 : IsOrth X x0)
    {W : Frame X.Ψ r → ℝ≥0∞} {Ps : Frame X.Ψ r → ℝ} {g1 : V (nd X) → ℂ} {bb m : ℝ} (hbb : 0 < bb)
    (hm : bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) + bb < m)
    (hg1 : DifferentiableOn ℂ g1 (OmF X x0))
    (hPs : ContDiffOn ℝ ∞ (fun z => Ps (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ g1 z ≠ 0})
    (hWPs : ∀ z, z ∈ OmF X x0 → g1 z ≠ 0 →
      W (cpt X x0 z) = ENNReal.ofReal (Real.exp (-Ps (cpt X x0 z))))
    (hLev : ∀ z, z ∈ OmF X x0 → g1 z ≠ 0 → ∀ ξ : Fin (nd X) → ℂ,
      m * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) z ξ).re ≤
        (leviV (nd X) (fun w => ((Ps (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re)
    {f0 : Frame X.Ψ r → ℂ} (hf0 : DifferentiableOn ℂ f0 X.dom) :
    ∃ F' : V (nd X) → ℂ, DifferentiableOn ℂ F' (Om1 X x0 g1) ∧
      ∫⁻ z in Om1 X x0 g1, ENNReal.ofReal (‖(kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) - F' z‖ ^ 2 /
          kaF X x0 bb z) * W (cpt X x0 z) ∂muF X x0 ≤
        ENNReal.ofReal (bb ^ 2 * ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) / (m - bb)) *
          ∫⁻ z in Om1 X x0 g1, ENNReal.ofReal (kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2) *
            W (cpt X x0 z) ∂muF X x0 := by
  set C : ℝ := ((X.Ψ.card * min X.p0 (r - X.p0) : ℕ) : ℝ) with hCdef
  have hC0 : 0 ≤ C := Nat.cast_nonneg _
  have hmb : 0 < m - bb := by nlinarith [mul_nonneg (sq_nonneg bb) hC0]
  set q : ℝ := bb ^ 2 * C / (m - bb) with hqdef
  have hq0 : 0 ≤ q := div_nonneg (mul_nonneg (sq_nonneg _) hC0) hmb.le
  have key : q * (m - bb) = bb ^ 2 * C := by rw [hqdef]; field_simp
  have hU := isOpen_nonvanishingLocus X x0 hg1
  obtain ⟨S, hSz, -⟩ := hExG r X x0 hx0 g1 hg1
  have hsubU : Om1 X x0 g1 ⊆ OmF X x0 := fun z hz => hz.1
  set PL : V (nd X) → ℝ := fun z => Ps (cpt X x0 z) - Real.log (densF X x0 z) with hPL
  set ph : V (nd X) → ℝ := fun z => PL z + (-bb) * rhF X x0 z with hph_def
  set F0 : V (nd X) → ℂ := fun z => (kaF X x0 bb z : ℂ) * f0 (cpt X x0 z) with hF0_def
  set hr : V (nd X) → ℝ := fun z => q * (kaF X x0 bb z ^ 2 * ‖f0 (cpt X x0 z)‖ ^ 2) with hr_def
  have hPsA : ∀ z ∈ Om1 X x0 g1, ContDiffAt ℝ ∞ PL z := fun z hz =>
    (hPs.contDiffAt (hU.mem_nhds hz)).sub (logDens_contDiffAt hz.1)
  have hrhA : ∀ z ∈ Om1 X x0 g1, ContDiffAt ℝ ∞ (rhF X x0) z := fun z hz => rhF_contDiffAt hz.1
  have hlevi : ∀ y ∈ Om1 X x0 g1, ∀ ξ, (leviV (nd X) (fun w => (ph w : ℂ)) y ξ).re =
      (leviV (nd X) (fun w => (PL w : ℂ)) y ξ).re +
        (-bb) * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) y ξ).re := by
    intro y hy ξ
    have h1 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add (f := PL) (g := fun w => (-bb) * rhF X x0 w)
      ((hPsA y hy).of_le (WithTop.coe_le_coe.2 le_top)) ((contDiffAt_const.mul (hrhA y hy)).of_le (WithTop.coe_le_coe.2 le_top)) ξ
    have h2 := ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul (-bb) ((hrhA y hy).of_le (WithTop.coe_le_coe.2 le_top)) ξ
    rw [h1, h2, Complex.add_re, Complex.re_ofReal_mul]
  have hpsh : ∀ y ∈ Om1 X x0 g1, ∀ ξ, 0 ≤ (leviV (nd X) (fun w => (ph w : ℂ)) y ξ).re := by
    intro y hy ξ
    rw [hlevi y hy ξ]
    have h1 := hLev y hy.1 hy.2 ξ
    have h2 := levi_rh_nonneg hGrad hx0 hy.1 ξ
    nlinarith
  have hph : ContDiffOn ℝ ∞ ph (Om1 X x0 g1) := fun z hz =>
    ((hPsA z hz).add (contDiffAt_const.mul (hrhA z hz))).contDiffWithinAt
  have hg : DifferentiableOn ℂ (fun z => f0 (cpt X x0 z)) (OmF X x0) := hol_comp X x0 hf0
  have hgc : ContDiffOn ℂ ∞ (fun z => f0 (cpt X x0 z)) (OmF X x0) := contDiffOn_of_differentiableOn _ _ _ (isOpen_OmF X x0) hg
  have hF0 : ContDiffOn ℝ ∞ F0 (Om1 X x0 g1) := fun z hz =>
    ((Complex.ofRealCLM.contDiff.contDiffAt.comp z (ka_contDiffAt bb hz.1)).mul
      ((hgc.contDiffAt ((isOpen_OmF X x0).mem_nhds hz.1)).restrict_scalars ℝ)).contDiffWithinAt
  have hrc : ContinuousOn hr (Om1 X x0 g1) := by
    refine continuousOn_const.mul (ContinuousOn.mul ?_ ?_)
    · exact fun z hz => ((ka_contDiffAt bb hz.1).continuousAt.pow 2).continuousWithinAt
    · exact (hg.continuousOn.mono hsubU).norm.pow 2
  have hr0 : ∀ y ∈ Om1 X x0 g1, 0 ≤ hr y := fun y _ => mul_nonneg hq0 (by positivity)
  have hineq : ∀ y ∈ Om1 X x0 g1, ∀ ξ : Fin (nd X) → ℂ,
      ‖∑ j, wdb (nd X) j F0 y * conj (ξ j)‖ ^ 2 ≤ hr y * (leviV (nd X) (fun w => (ph w : ℂ)) y ξ).re := by
    intro y hy ξ
    rw [hF0_def, dbar_ka X x0 bb hf0 hy.1 ξ, hlevi y hy ξ]
    set s := ∑ j, wd (nd X) j (fun w => ((rhF X x0 w : ℝ) : ℂ)) y * ξ j
    have hG := hGrad r X x0 hx0 y hy.1 ξ
    have hL := hLev y hy.1 hy.2 ξ
    have e1 : ‖((-bb * kaF X x0 bb y : ℝ) : ℂ) * f0 (cpt X x0 y) * conj s‖ ^ 2 =
        bb ^ 2 * kaF X x0 bb y ^ 2 * ‖f0 (cpt X x0 y)‖ ^ 2 * Complex.normSq s := by
      rw [norm_mul, norm_mul, Complex.norm_real, RCLike.norm_conj, mul_pow, mul_pow, Real.norm_eq_abs,
        sq_abs]
      simp only [Complex.sq_norm]
      ring
    rw [e1]
    calc bb ^ 2 * kaF X x0 bb y ^ 2 * ‖f0 (cpt X x0 y)‖ ^ 2 * Complex.normSq s
        ≤ bb ^ 2 * kaF X x0 bb y ^ 2 * ‖f0 (cpt X x0 y)‖ ^ 2 *
            (C * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) y ξ).re) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ = hr y * ((m - bb) * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) y ξ).re) := by
          simp only [hr_def]; linear_combination (kaF X x0 bb y ^ 2 * ‖f0 (cpt X x0 y)‖ ^ 2 *
            (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) y ξ).re) * (-key)
      _ ≤ hr y * ((leviV (nd X) (fun w => (PL w : ℂ)) y ξ).re +
            (-bb) * (leviV (nd X) (fun w => ((rhF X x0 w : ℝ) : ℂ)) y ξ).re) :=
          mul_le_mul_of_nonneg_left (by nlinarith) (hr0 y hy)
  obtain ⟨F', hF', hest⟩ := horm_open hU S hSz ph F0 hr hph hpsh hF0 hrc hr0 hineq
  refine ⟨F', hF', ?_⟩
  rw [setLIntegral_muF X x0 hU.measurableSet hsubU, setLIntegral_muF X x0 hU.measurableSet hsubU,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine le_trans (le_of_eq ?_) (hest.trans (le_of_eq ?_))
  · refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
    have hd := densF_pos hz.1
    have hk : 0 < kaF X x0 bb z := Real.exp_pos _
    rw [hWPs z hz.1 hz.2, ofReal_mul_ofReal_nonneg (by positivity), ofReal_mul_ofReal_nonneg hd.le, hph_def]
    simp only
    rw [exp_ph X x0 (fun w => Ps (cpt X x0 w)) bb hz.1]
    simp only [hF0_def]
    congr 1
    field_simp
  · refine setLIntegral_congr_fun hU.measurableSet fun z hz => ?_
    have hd := densF_pos hz.1
    have hk : 0 < kaF X x0 bb z := Real.exp_pos _
    rw [hWPs z hz.1 hz.2, ← ENNReal.ofReal_mul (hr0 z hz),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ kaF X x0 bb z * ‖f0 (cpt X x0 z)‖ ^ 2),
      ← ENNReal.ofReal_mul hd.le, ← ENNReal.ofReal_mul hq0, hph_def]
    simp only
    rw [exp_ph X x0 (fun w => Ps (cpt X x0 w)) bb hz.1, hr_def]
    congr 1
    field_simp

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.OntoC
