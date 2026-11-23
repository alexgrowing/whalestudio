import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
open CategoryTheory AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory

open CategoryTheory AlgebraicGeometry in

theorem _root_.GlobalTheory.lawsFieldsSeparately :
    _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalSectionsRankAlgClosed ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.AmpleSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.KerPowSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.MulPullSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.MulNSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.CubeSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SquareSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.RigiditySt ∧
      _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.WeilNondegSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SymLiftSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.IrredSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.GoodPtSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SerreSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.GlobalFnsSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.PolBaseChangeSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.QuotientSt ∧
      _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeAnySt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.CharPairSt ∧ _root_.ReciprocityTheory.ChartRestriction.G.Out.SmoothDenseSt := by
  obtain ⟨h₁, h₂, -⟩ := _root_.GlobalTheory.allSixLaws
  exact ⟨h₁.globalSectionsRank, h₁.secBaseChange, h₁.ample, h₁.kerPow, h₁.mulPull, h₁.mulN, h₁.cube,
    h₁.square, h₁.rigidity, h₁.weil, h₁.weilNondeg, h₁.symLift, h₁.irred, h₁.goodPt, h₁.serre,
    h₁.globalFns, h₁.polBaseChange, h₁.quotient, h₂.secBaseChangeAny, h₂.secTwist, h₂.charPair,
    h₂.smoothDense⟩

end GlobalTheory
