import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CoeffOfJet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StarRingExtOfStar
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProductStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ConstBFMul

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem germOfFam_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → GermOfFamT := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c inst hstar
  obtain rfl := starSt E H inst hstar
  let := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ v hv q hq
  have hu := GlobalTheory.T.universalJets_power_product T.V C.I.G.G G' n _ pG C.xT (GlobalTheory.T.universal_statement E H Dw l Xo c T io y C)
  obtain ⟨τ, hτ, ht, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
    C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  refine ⟨fun σ' => ?_, fun s σ' hE hs g hg => ?_⟩
  · obtain ⟨f, hf⟩ := (GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hu τ hτ F q).2.2 (ht htr) σ'
    exact ⟨f, (hiff F q σ' f).2 hf⟩
  · exact GlobalTheory.IntegralGerm.main hL hL2 hL4 hT T.V ϖ hϖ D' A' G' U' _ _ hu τ hτ F v hv q hq σ' s g hE
      ((hiff F q σ' g).1 hg)
      (n1e T.V ϖ hϖ D' _ (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v q s hs)

end GlobalTheory.PowGerm
