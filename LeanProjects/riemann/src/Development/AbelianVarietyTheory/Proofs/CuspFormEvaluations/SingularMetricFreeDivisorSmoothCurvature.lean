import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LocalUnfoldBStatementHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContDiffAtCompCpt

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology GlobalTheory.Shares
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Shares

open GlobalTheory.Up.DivLeviPf in

theorem divLevi_freeWeight : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (n : ℕ), 1 ≤ n → ∀ x0, IsOrth X x0 → (∃ k0, ∃ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0) ∧ ∀ k0 : Fin (nd X), ContDiffOn ℝ ∞ (fun z => (fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 z)) {z | z ∈ OmF X x0 ∧ Fl.s k0 (cpt X x0 z) ≠ 0} ∧ ∀ z ∈ OmF X x0, Fl.s k0 (cpt X x0 z) ≠ 0 → ∀ ξ : Fin (nd X) → ℂ, leviO X x0 (phla X G) z ξ - leviDens X x0 z ξ ≤ (leviV (nd X) (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) + ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) - Real.log (densF X x0 w) : ℝ) : ℂ)) z ξ).re := by
  intro E _ _ _ r X Xa Fl G n hn x0 ho
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
  · have h1 := IW.phla_cpt_cdAt X x0 hz.1 G
    have h2 := logSum_contDiffAt (hw z hz.1) (Xa.w_nz _ hz.1)
    have h3 := logSum_contDiffAt (hs z hz.1) ⟨k0, hz.2⟩
    exact ((h1.add (contDiffAt_const.mul h2)).add (contDiffAt_const.mul h3)).contDiffWithinAt
  · have h1 := (IW.phla_cpt_cdAt X x0 hz G).of_le HE.two_le_inf
    have h2 := (logSum_contDiffAt (hw z hz) (Xa.w_nz _ hz)).of_le HE.two_le_inf
    have h3 := (logSum_contDiffAt (hs z hz) ⟨k0, hz0⟩).of_le HE.two_le_inf
    have h4 := (IW.logDens_cdAt X x0 hz).of_le HE.two_le_inf
    have l2 := logSum_levi_nonneg (hw z hz) (Xa.w_nz _ hz) ξ
    have l3 := logSum_levi_nonneg (hs z hz) ⟨k0, hz0⟩ ξ
    have e : (fun w => (((fun x => phla X G x + (1 / 2) * Real.log (∑ k, ‖Xa.w k x‖ ^ 2) +
          ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k x‖ ^ 2)) (cpt X x0 w) -
            Real.log (densF X x0 w) : ℝ) : ℂ)) =
        fun w => (((phla X G (cpt X x0 w) + (-1) * Real.log (densF X x0 w)) +
          ((1 / 2) * Real.log (∑ k, ‖Xa.w k (cpt X x0 w)‖ ^ 2) +
            ((n : ℝ) - 1 / 2) * Real.log (∑ k, ‖Fl.s k (cpt X x0 w)‖ ^ 2)) : ℝ) : ℂ) := by
      funext w
      congr 1
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

end GlobalTheory.Shares
