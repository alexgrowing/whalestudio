import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.CuspFormHalfSupAtOrthonormalFrameFirstMinStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.LogExpMulLeOfGeneratorSupBound
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBoundsStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.NormShortGeneratorEvalLeOrthonormalFrameStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EqZeroOfForallAlgHom

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

set_option maxHeartbeats 800000 in

theorem log_sup_short_generator_le : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T), GamAt T.toCore → ∀ (large₂ : SizeData₂ D) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), ReciprocityTheory.ChartRestriction.G.PullbackSections.SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L → D.R.r ≤ w.n → LastPos (T.Q.Dw j) (wtA w) → LawsSh T → (T.dδ j w.n).l₂.A = 1 → ∀ (Λ : GenLat D.host.E w.n) (N : ℕ) (x0 : Fin w.n → (T.Q.Dw j).La) (P : MvPolynomial (LtN (T.Q.Dw j) w.n) T.Q.c.F) (g : T.R j), Λ.Unimod → Λ.TrivAt (badN D) → Λ.TrivAt (T.dδ j w.n).l₂.M → Λ.LevOK N (T.dδ j w.n).l₂.M → AdmX (l := T.Q.l) (decide (w.n = D.R.nV)) x0 → P ∈ harmL T.Q.c Λ (wtA w) → IsShortRule (T.Q.Xo j) T.Q.c (T.dδ j w.n) Λ N x0 P g → g ∈ sec (T.Q.Xo j) T.Q.c (wtA w) w.n → ∀ (σ : T.Q.c.F →+* ℂ) (ℓ : ℝ), 0 ≤ ℓ → l1At σ P ≤ Real.exp ℓ → Real.log (T.Ns j w σ g) ≤ ℓ + 10 * large₂.sc.L * absA w + 200 * D.R.f * D.R.r * w.n * large₂.sc.L := by
  intro hCh D T hT hG large₂ j hj w hRows hL hr hLast hSh hA Λ N x0 P g hU hTb hTM hLev hX hP hS hg σ ℓ hℓ hl1
  obtain ⟨hfd, hrd, hrd1, hf1, hr1, hxi, hDF, habs, hc, hlie, hlA, hpde, hpde', hl1g⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T hT j hj w
  have hRw := hRows
  obtain ⟨-, hlrd, -, -, hlf, hlp, hlp', hlDF, hln⟩ := hRows
  set σ' := goodOf T.Q.c σ with hσ'
  have hgood : GoodEmb T.Q.c σ' := goodEmb_goodOf _ σ
  have hgC : g ∈ T.C j w :=
    hSh.8 j hj (wtA w) w.n (dom_wtA w) hLast (dom_wtA w) hLast ⟨hg, Λ, N, x0, P, hU, hTb, hTM, hLev, hX, hP, hS⟩
  obtain ⟨Cls, _, _, δ, gdet, hcmp⟩ := hSh.6 j hj w.n
  have hUC : GlobalTheory.Dict.UnitC (T.dδ j w.n) := FiniteOrderRule.unitC_of_cmp _ _ _ _ _ _ _ _ Cls δ gdet hcmp
  obtain ⟨p, hp, hpd⟩ := hSh.4
  have hpdw : (T.dδ j w.n).pd = p := hpd j hj w.n
  have hp0 : 0 < p := by rcases hp with rfl | rfl <;> assumption
  have hlogp : Real.log p ≤ large₂.sc.L := by rcases hp with rfl | rfl <;> assumption
  obtain ⟨ph, ψ, xψ, -, hpin, -⟩ := hSh.5 j hj w.n hr
  have hunf : IsUnf (T.U j σ') := hT.unf j hj σ' hgood
  have hNs : T.Ns j w σ g = lieFac (T.Q.Dw j) (xiR D) (wtA w) *
      supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) := rfl
  rw [hNs, hlie]
  set S := supN (T.U j σ').X (laU (T.U j σ') (wtA w) w.n) (rdU (T.U j σ') g) with hSdef
  have hS0 : 0 ≤ S := by rw [hSdef]; unfold supN; exact ENNReal.toReal_nonneg
  have hL0 : (0:ℝ) ≤ large₂.sc.L := by linarith
  have ha0 : (0:ℝ) ≤ absA w := by rw [habs]; positivity
  rcases hS0.eq_or_lt with hS00 | hSpos
  · rw [← hS00, mul_zero, Real.log_zero]
    positivity
  obtain ⟨k, xf, -, hortho, hSle, hla, hlog⟩ :=
    GlobalTheory.T.cuspForm_halfSup_at_orthonormalFrame_firstMin D T hT hG large₂ j hj w hRw hL hr hLast σ' hgood g hgC hSpos
  set lam := Real.sqrt (((T.U j σ').X k).firstMinimumSq xf.1) with hlam
  have hlam0 : 0 < lam := Real.sqrt_pos.mpr hla
  have hlam2 : lam ^ 2 = ((T.U j σ').X k).firstMinimumSq xf.1 := Real.sq_sqrt hla.le
  have hv := GlobalTheory.T.norm_short_generator_eval_le_orthonormal_frame hCh D.host.E T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c σ' D.R.r
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ')) ((Formalism.L2.PjFree.goodEmb_iff σ').mpr hgood)
    ((Formalism.L2.PjFree.isUnf_ofPj _).mpr hunf) hr1 (2 * xiR D) (by linarith) (hc σ' hgood) (wtA w) w.n
    (dom_wtA w) hr (T.dδ j w.n) (hSh.2 j hj w.n) (by rw [hpdw]; exact hp0) hlA hA (hSh.3 j hj w.n)
    ⟨ph, ψ, xψ, hpin⟩ hUC Λ N x0 P g hU hTM hLev (hSh.1 j hj w.n (hT.kPsi j hj) Λ hU hTb) hP hS
    k xf hortho lam hlam0 hlam2.le
  have hp1eq : (∑ m ∈ P.support, ‖σ' (P.coeff m)‖) = l1At σ P := hl1g _ σ P
  rw [hfd, hp1eq] at hv
  have hcle : ((T.dδ j w.n).pd : ℝ) ^ (D.R.f * D.R.r * w.n) ≤
      Real.exp (D.R.f * D.R.r * w.n * large₂.sc.L) := by
    rw [hpdw]
    have hp' : (0:ℝ) < p := by exact_mod_cast hp0
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hp']
    apply Real.exp_le_exp.mpr
    push_cast
    have hfrn : (0:ℝ) ≤ D.R.f * D.R.r * w.n := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogp hfrn]
  have hp1 : 0 ≤ l1At σ P := by unfold l1At; exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  exact GlobalTheory.log_exp_mul_le_of_generator_sup_bound D.R.f D.R.r w.n (Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w))
    large₂.sc.L ℓ (absA w) (rdE D.host.E) lam (2 * xiR D) _ S _ (l1At σ P) hL hf1 hr1 hr
    (by rw [habs]; exact_mod_cast hDF) (by rw [habs]; exact hlDF) hln hlf hrd1 (by rw [hrd]; exact hlrd)
    hlam0 (by rw [hlam2]; exact hlog) (by linarith) hℓ hp1 hl1 (by positivity) hcle hS0 hSle hv

end GlobalTheory.RunIn
