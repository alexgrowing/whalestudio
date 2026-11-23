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

namespace GlobalTheory

theorem noCommonZero_of_chartIndep : Formalism.MainNotions.ModuliIntegralCharts.H1.ChartIndepSt2 → NoCommonZeroSt := by
  intro hC D T h j hj w hn _hlast hM _hα σ hσ k x hx

  obtain ⟨-, -, -, -, hr1, hxi, hDF, -, hc, -⟩ := GlobalTheory.T.unitaryDatumNumbers_for_supBounds D T h j hj w

  obtain ⟨st, hnab⟩ := h.nabPin j hj

  obtain ⟨f, hf, hne⟩ := GlobalTheory.T.exists_thetaGenerator_reading_ne_zero_at_frame hC _ _ _ _ _ _ σ D.R.r (Formalism.L2.PjFree.Unf.ofPj (T.U j σ))
    ((Formalism.L2.PjFree.goodEmb_iff σ).mpr hσ) ((Formalism.L2.PjFree.isUnf_ofPj _).mpr (h.unf j hj σ hσ)) hr1
    (2 * xiR D) (by linarith) (fun k τ => hc σ hσ k τ) (wtA w) w.n (dom_wtA w) hn (by omega) st (T.nab j)
    hnab k x hx
  exact ⟨f, hf, by rwa [Formalism.L2.PjFree.rdU_ofPj] at hne⟩

end GlobalTheory
