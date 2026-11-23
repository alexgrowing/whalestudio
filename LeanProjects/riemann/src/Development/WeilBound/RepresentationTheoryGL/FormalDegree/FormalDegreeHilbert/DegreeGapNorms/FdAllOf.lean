import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.DiscreteSeriesSU.GapInv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.HighestWeights.Exists
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.ExistsMu

noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace

namespace PositivityTheory.RgFd

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7

theorem fdAll_of (hM : ModelDS) (hF : FdModel) : FdAll := by
  intro n ε lam hl H _ _ σ hσ
  obtain ⟨T⟩ := HW.kType_exists ε lam hl
  obtain ⟨μ, hμ⟩ := S7.exists_mu hl
  have hDS := (hM n ε lam T μ hl hμ).2
  have hd := hF n ε lam T μ hl hμ
  obtain ⟨U, hU⟩ := PositivityTheory.DiscreteSeriesGap.GapInv.dsUnique_dec n ε lam H σ _ (sigLam ε (PsiM T μ) T.w) hl hσ hDS
  have hc : ∀ (v w : H) (g : Formalism.REAL.UJ ε), Formalism.MainNotions.S.coefOn σ v w g =
      Formalism.MainNotions.S.coefOn (sigLam ε (PsiM T μ) T.w) (U v) (U w) g := by
    intro v w g
    simp only [Formalism.MainNotions.S.coefOn]
    rw [← hU _ g.2 v, LinearIsometryEquiv.inner_map_map]
  refine ⟨hd.1, fun v w v' w' => ?_⟩
  obtain ⟨h1, h2⟩ := hd.2 (U v) (U w) (U v') (U w')
  simp only [hc]
  refine ⟨h1, ?_⟩
  rw [h2, LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]

end PositivityTheory.RgFd
