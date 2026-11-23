import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.CstSmoothOfEtSide
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsCrystallineChernClassLimit

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct
open GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison

def EtMapP : Prop := ∀ (l : ℕ) [Fact l.Prime] (K : IntermediateField ℚ_[l] (PadicAlgCl l)) (ζ : E.Roots l),
  ∃ e : E.EtFam l K, e.Good ∧ (∀ (M : Model l K) n, e M n 0 (GlobalTheory.EtC.one (l ^ n) _) = CH.oneH _) ∧
    (∀ (M : Model l K) D v, HT.IsEtaleFirstChernUntwisted ζ D v → E.IsFirstChernClassOfLineBundle M.p (okToOC l K) D (e.tMul M v)) ∧
    (∀ (M : Model l K) (D : E.LineData M.X), ∃ v, HT.IsEtaleFirstChernUntwisted ζ D v) ∧
    ∀ M : Model l K, ∃ v : M.T 0, ∀ k, v.lev k = GlobalTheory.EtC.one _ _

def GlueP : Prop := BcrisPeriodFacts → EtSideS → Chapters → EtMapP → FSeamP → CrysPhiP

end CrystallineSemistableComparison
