import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcLineFunctions.ArcDatumIsArcPointBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FundamentalDomainPointBound
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.ModelLat

noncomputable section

open NumberField Formalism.L2.Pj Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.PullbackSections

namespace Formalism.L2.Pj.QAt

variable {D : D7}

def DataXOfModelSt (T : Top D) (j : ℕ) : Prop :=
  ∀ (_h : LawsCore T.toCore), ReciprocityTheory.ChartRestriction.G.PullbackSections.GamAt T → InR D j → ∀ (large₂ : SizeData₂ D) (w : WeightFamilies.Wt D j), SupBoundPageRows D large₂ w → 2 ≤ large₂.sc.L →
    ∀ (σ₀ : T.Q.c.F →+* ℂ), GoodEmb T.Q.c σ₀ → ∀ (k : (T.U j σ₀).Comp),
    ∃ Xx : DataX D.host.E D.R.r, Xx.toData = (T.U j σ₀).X k ∧ Xx.g = T.Q.l.M ∧
      Real.log Xx.NA ≤ (fdeg D.host.E : ℝ) * Real.log (rdE D.host.E) ∧ Real.log Xx.NC ≤ 2 * large₂.sc.L ∧
      Xx.Λ = Submodule.span (𝓞 D.host.E) {v | ∃ a ∈ D.host.AA, ∃ u ∈ Xx.L', v = a • u}

end Formalism.L2.Pj.QAt
