import Mathlib
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.CarchAt
import Development.AbelianVarietyTheory.Definitions.ThetaValues.Generic
import Formalism.LocalToGlobal.ProjectiveLattices.TieUpA
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.LinkFD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.SiegelSpaceAlgebraHolds
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CuspFormFrameReadingsLinearIndependent
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.Pj.QAt Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions GlobalTheory.ArcCM GlobalTheory.Shares

namespace GlobalTheory.ArcRead

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem readings_cusp_and_independent :
    ∀ (D : D7) (T : Top D) (h : LawsP T) (j : ℕ), InR D j → TieReadSt h j := by
  intro D T h j hj
  refine ⟨fun u F k => ?_, fun u => GlobalTheory.Dict.readings_independent D T h.toLawsM j hj _ _⟩
  have hFC : F.1 ∈ T.C j u := cutR_le T.C j u F.2
  have hhol : rdU (T.U j T.σ₀) F.1 ∈ holSub (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) :=
    ((mem_cusp _ _ _ _ _ F.1).1 hFC).2 T.σ₀ T.good_σ₀
  exact Formalism.L2.Pj.abelian₂.holSub_SS siegelSpaceAlgebra_holds (T.U j T.σ₀).X (laU (T.U j T.σ₀) (wtA u) u.n) hhol k

end GlobalTheory.ArcRead
