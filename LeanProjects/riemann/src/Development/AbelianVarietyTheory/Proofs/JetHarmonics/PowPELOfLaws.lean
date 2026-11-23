import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPelUnifOfUnifPow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsMulEquivPointsOfIsPowGrp
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TwistingStatementsOfLaws
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBasisOfCoord
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValuationThetaRatioEqBilinear
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionIsoOfLinearUniformisationTripleStatement

set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem powPEL_of_laws : Laws → Laws2 → Laws3 → Laws4 → Laws5 → TwistBaseChangeStatement → PowPELF := by
  intro h₁ h₂ h₃ h₄ h₅ hT E _ _ _ H Dw l Xo c n T io y _ C P _ g g' _ _ _ _ _ π π' _ _ _ _ _ F _ _ _ _ _ _ v ϖ hϖ _ I Q hQ
    D' A' G' _ _ pD pA pG U' PU _ oD' hx hB
  letI := H.starRing
  have hA : AdmBase T.V (maximalIdeal T.V) := ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩
  obtain ⟨oA', hoA, t', P', hP'⟩ :=
    GlobalTheory.exists_pelUnif_of_unifPow h₁ h₂ h₄ hT T.V E H C.I.G P n D' A' G' pD pA pG U' PU oD' hx hB
  refine ⟨oA', hoA, GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ,
    GlobalTheory.exists_tateIso_of_isPowPolAV h₁ h₂ h₄ hT E H T.V n P.A A' pA F _ _ hoA Dw I, t', P', ?_, hP'⟩
  exact GlobalTheory.T.torsionIso_of_linear_uniformisation_triple ⟨h₁, h₂, h₃, h₄, h₅⟩ (twistBCSpan_of hT) GlobalTheory.RatioVal.main
    (GlobalTheory.twisting_statements_of_laws h₁ hT).1 (GlobalTheory.UnitBallFree.main h₁.globalFns hT) E H T.V _ hA t' P'

end GlobalTheory.PowGerm
