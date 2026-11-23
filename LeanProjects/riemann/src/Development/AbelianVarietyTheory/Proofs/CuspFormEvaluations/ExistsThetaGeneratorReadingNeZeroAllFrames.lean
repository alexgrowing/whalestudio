import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupGenTies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaGeneratorReadingNeZeroAtFrameStatement
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.UnitaryDatumNumbersForSupBoundsStatement

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections GlobalTheory.RunIn

namespace GlobalTheory.RunIn

theorem exists_theta_ne_zero_record : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (w : WeightFamilies.Wt D j), D.R.r ≤ w.n → 3 * WeightAlgebra.DF w + 2 ≤ T.Q.l.M → ∀ (σ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ → ∀ k, ∀ x ∈ ((T.U j σ).X k).dom, ∃ f ∈ T.th j w, rdU (T.U j σ) f k x ≠ 0 := by
  intro hC D T h j hj w hn hM σ hσ k x hx
  obtain ⟨_, _, _, _, hr1, hxi, hDF, _, hc, _⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T h j hj w
  obtain ⟨st, hnab⟩ := h.nabPin j hj
  obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame hC _ _ _ _ (T.Q.Xo j) T.Q.c σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).2 hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).2 (h.toLawsCore.unf j hj σ hσ)) hr1
    (2 * xiR D) (mul_pos two_pos hxi) (hc σ hσ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j) hnab k x hx
  refine ⟨f, hf, ?_⟩
  rwa [Formalism.L2.PjFree.rdU_ofPj] at hne

end GlobalTheory.RunIn
