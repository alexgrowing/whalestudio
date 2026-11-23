import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KronHolPsiStatementHolds
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.DerivDerivNonposOfIsLocalMax

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up

namespace DivLeviPf

section Euclid

variable {n p : ℕ} {g : Fin p → V n → ℂ} {y : V n}

theorem logSum_contDiffAt (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0) :
    ContDiffAt ℝ ∞ (fun w => Real.log (∑ k, ‖g k w‖ ^ 2)) y := by
  have h1 : ContDiffAt ℝ ∞ (fun w => ∑ k, ‖g k w‖ ^ 2) y := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (hg k)
  exact h1.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg (hg : ∀ k, ContDiffAt ℂ ∞ (g k) y) (hne : ∃ k, g k y ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) y ξ).re := by
  obtain ⟨k0, hk0⟩ := hne
  have h := leviLogNormSq n p g y ξ (fun k => (hg k).of_le HE.two_le_inf)
    (fun h => hk0 (congrFun h k0))
  have e : (fun w => ((Real.log (∑ k, ‖g k w‖ ^ 2) : ℝ) : ℂ)) =
      fun w => ((Real.log (sqNorm (fun i => g i w)) : ℝ) : ℂ) := by
    funext w
    simp only [← Complex.normSq_eq_norm_sq]
    rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

end Euclid

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem contDiffAt_comp_cpt {P : Frame X.Ψ r → ℂ} (hP : DifferentiableOn ℂ P X.dom)
    (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℂ ∞ (fun w => P (cpt X x0 w)) z := by
  have hc : Differentiable ℂ (cpt X x0) :=
    differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
      (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)
  exact HE.contDiffAt_of_punct (ExF.isOpen_OmF X x0)
    (hP.comp hc.differentiableOn fun w hw => hw) hz

theorem exists_s_ne_zero {Xa : ArchInM X} (Fl : FlatM X Xa) {x0 : Frame X.Ψ r} (hx0 : x0 ∈ X.dom) :
    ∃ k, ∃ x ∈ X.dom, Fl.s k x ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨j, -⟩ := (Fl.S_eq x0 hx0).1 fun k => h k x0 hx0
  have h0 : (0 : V (nd X)) ∈ OmF X (Fl.xs j) := by
    show cpt X (Fl.xs j) 0 ∈ X.dom
    rw [IW.cpt_zero]
    exact Fl.xs_mem j
  have hev : (fun z : V (nd X) => (WithLp.toLp 2 fun k =>
      Fl.s k (cpt X (Fl.xs j) z) / Fl.w0 (cpt X (Fl.xs j) z) : V (nd X))) =ᶠ[𝓝 0] fun _ => 0 := by
    filter_upwards [(ExF.isOpen_OmF X (Fl.xs j)).mem_nhds h0] with w hw
    ext k
    simp [h k _ hw]
  apply Fl.coord j
  rw [hev.fderiv_eq, fderiv_fun_const]
  have h2 := Xa.n_ge
  have : Nonempty (Fin (nd X)) := ⟨⟨0, by omega⟩⟩
  show LinearMap.det (0 : V (nd X) →ₗ[ℂ] V (nd X)) = 0
  exact LinearMap.det_zero' (EuclideanSpace.basisFun (Fin (nd X)) ℂ).toBasis

end DivLeviPf

open DivLeviPf in

theorem divLevi_holds {E : Type} [Field E] [NumberField E] [IsCMField E] : DivLevi (E := E) := by
  intro r X Xa Fl n hn x0 ho
  have hsS : ∀ k, X.IsSec Xa.L (Fl.s k) := fun k => (Fl.s_van k).1.1.1
  have hwS : ∀ k, X.IsSec Xa.L (Xa.w k) := fun k => (Xa.w_van k).1.1.1
  have hs : ∀ z ∈ OmF X x0, ∀ k, ContDiffAt ℂ ∞ (fun w => Fl.s k (cpt X x0 w)) z :=
    fun z hz k => contDiffAt_comp_cpt (hsS k).1 x0 hz
  have hw : ∀ z ∈ OmF X x0, ∀ k, ContDiffAt ℂ ∞ (fun w => Xa.w k (cpt X x0 w)) z :=
    fun z hz k => contDiffAt_comp_cpt (hwS k).1 x0 hz
  refine ⟨?_, fun k0 => ⟨fun z hz => ?_, fun z hz hz0 ξ => ?_⟩⟩
  · obtain ⟨k, x, hx, hne⟩ := exists_s_ne_zero Fl (IW.orth_mem_dom X x0 ho)
    by_contra h
    push Not at h
    exact hne (bigCellStatement_holds r X x0 ho Xa.L (Fl.s k) ⟨(hsS k).1, (hsS k).2.1⟩ (h k) x hx)
  · have h1 := IW.phla_cpt_cdAt X x0 hz.1 Xa.Fp
    have h2 := logSum_contDiffAt (hw z hz.1) (Xa.w_nz _ hz.1)
    have h3 := logSum_contDiffAt (hs z hz.1) ⟨k0, hz.2⟩
    exact ((h1.add (contDiffAt_const.mul h2)).add (contDiffAt_const.mul h3)).contDiffWithinAt
  · have h1 := (IW.phla_cpt_cdAt X x0 hz Xa.Fp).of_le HE.two_le_inf
    have h2 := (logSum_contDiffAt (hw z hz) (Xa.w_nz _ hz)).of_le HE.two_le_inf
    have h3 := (logSum_contDiffAt (hs z hz) ⟨k0, hz0⟩).of_le HE.two_le_inf
    have h4 := (IW.logDens_cdAt X x0 hz).of_le HE.two_le_inf
    have l2 := logSum_levi_nonneg (hw z hz) (Xa.w_nz _ hz) ξ
    have l3 := logSum_levi_nonneg (hs z hz) ⟨k0, hz0⟩ ξ
    have e : (fun w => ((Psdiv X Xa Fl n (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) =
        fun w => (((phla X Xa.Fp (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) +
          ((1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 w)‖ ^ 2) +
            ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k (cpt X x0 w)‖ ^ 2)) : ℝ) : ℂ) := by
      funext w
      congr 1
      unfold Psdiv
      ring
    rw [e, Y.LocalMaximumSecondDerivative.leviV_ofReal_add (h1.add (contDiffAt_const.mul h4))
        ((contDiffAt_const.mul h2).add (contDiffAt_const.mul h3)),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add h1 (contDiffAt_const.mul h4),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_add (contDiffAt_const.mul h2) (contDiffAt_const.mul h3),
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h4, Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h2,
      Y.LocalMaximumSecondDerivative.leviV_ofReal_const_mul _ h3]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    have hn' : (0 : ℝ) ≤ (n : ℝ) - 1 / 2 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    have l3' := mul_nonneg hn' l3
    unfold leviO leviM leviDens
    linarith

end GlobalTheory.Up
