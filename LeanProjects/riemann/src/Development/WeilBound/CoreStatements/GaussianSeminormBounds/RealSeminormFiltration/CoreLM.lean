import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreMain
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreSide
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreComb
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreNonv
import Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CorePair

noncomputable section

open ReciprocityTheory.ThetaSummability.Real ReciprocityTheory.ChartRestriction.G.ThK.Real FockH1Action MvPolynomial Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem coreLM : CoreLM := by
  intro D h
  obtain ⟨hn, hm, e1, e2, hP, hQ, hQ', hP'⟩ := nm_facts h
  have c1 : ((D.κ : ℂ) / 2) = (((D.κ : ℚ) / 2 : ℚ) : ℂ) := by push_cast; rfl
  have c2 : (-((D.κ : ℂ) / 2)) = ((-((D.κ : ℚ) / 2) : ℚ) : ℂ) := by push_cast; rfl
  have n1 : Nontrivial (ThV D) :=
    nontrivial_of_pair _ _ c1 (c1 ▸ pair_pos hP hQ hn hm _ e1 e2)
  have n2 : Nontrivial (ThV' D) :=
    nontrivial_of_pair _ _ c2 (c2 ▸ pair_neg hQ' hP' hn hm _ (by linarith) (by linarith))
  have s1 := side_of ((D.κ : ℂ) / 2) 0 _ 0 c1 (by simp) _ (combV h) n1
  have s2 := side_of (-((D.κ : ℂ) / 2)) ((D.κ : ℂ) / 2) _ _ c2 c1 _ (combV' h) n2
  rw [la_eq h] at s2
  obtain ⟨Pi, i1, i2, act, π, π', h1, h2, h3, h4, h5, h6⟩ := common_quot _ _ _ _ _ s1 s2
  refine ⟨Pi, i1, i2, act, π, π', h1, h2, fun W x => ?_, fun W x => h4 W x, h5, h6⟩
  rw [← h3 W x]
  congr 1
  simp [thAct, opV]

end PositivityTheory.KReal

end
