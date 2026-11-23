import Mathlib
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsCompletionOfCoreSatisfyingLaws
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemPerGrpOfIntegral
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.HarmonicGermValueChartIndependent
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ThInCuspCusp
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.FinalJoin GlobalTheory.CompRat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinalJoin

theorem thInCusp_of_laws (D : D7) (T : Core D) (h : LawsM T) (j : ℕ)
    (hj : InR D j) (inst : StarRing (𝓞 D.host.E)) (nab : NabV (T.Q.Xo j) T.Q.c)
    (hn : IsNab (T.Q.Xo j) T.Q.c nab) : ThInCusp (T.Q.Xo j) T.Q.c nab (T.cuspA j) := by
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    simp only [Ranks.r]; omega
  have hU : ∀ σ, Formalism.L2.PjFree.GoodEmb T.Q.c σ →
      Formalism.L2.PjFree.IsUnf (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) := fun σ hσ =>
    (Formalism.L2.PjFree.isUnf_ofPj _).2 (h.unf j hj σ ((Formalism.L2.PjFree.goodEmb_iff σ).1 hσ))
  exact @GlobalTheory.Dict.thInCusp_cusp GlobalTheory.harmonicValue_chart_independent D.host.E _ _ _ T.Q.H (T.Q.Dw j) T.Q.l (T.Q.Xo j) T.Q.c D.R.r
    (fun σ => Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) hr1 hU inst nab hn

theorem exists_top_of_core : ∀ (D : D7) (C : Core D), LawsCore C → (∀ j, 1 ≤ (C.Q.Dw j).p + (C.Q.Dw j).q) → OKPsi D → ∃ T : Top D, LawsP T ∧ T.toCore = C := by
  intro D C hC hpq hK
  exact GlobalTheory.Member.exists_completion_of_core_satisfying_laws GlobalTheory.harmonicValue_chart_independent D C hC hpq (hK C.Q hC.pins) (fun j hj inst nab hn =>
    ⟨thInCusp_of_laws D C hC.toLawsM j hj inst nab hn,
      fun _ => GlobalTheory.ThetaNeZero.thNe0_of_lawsM GlobalTheory.harmonicValue_chart_independent D C hC.toLawsM j hj inst nab hn⟩)

end GlobalTheory.FinalJoin
