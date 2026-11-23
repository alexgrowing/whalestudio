import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsThetaFrame
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiWeightZeroProduct
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ValFinProdGen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm

namespace GlobalTheory.PowThetaFrame

theorem main : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → ThetaFrameF := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c n T io y _ C P _ g g' _ hg' _ _ _ π π' _ hπ' _ _ _ F _ _ _ _ _ _ v ϖ hϖ hv
    Q hQ D' A' G' _ _ pD pA pG U' PU _ oD' hx hact
  let _ := H.starRing
  obtain ⟨θ, hν, hθ⟩ := exists_thetaFrame hL hL2 hL4 hT T.V ϖ hϖ D' (sumQ pD.xe Q)
    (QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v hv
  have hw : TraceFormTwistIso D'.toPre oD' H.w0 :=
    PsiWZeroProd.main T.V n P.D.toPre D'.toPre pD (𝓞 E) (fun a x => funext (hx a x)) P.oD oD' hact H.w0 P.w0
  obtain ⟨f, -, hf⟩ := PullLin.exists_pull_linearMap hL T.V D' F (𝓞 E) oD' H.w0 hw (star π') g' 1 hg'.one_le le_rfl
    (by rw [star_star, mul_comm]; exact hπ')
  exact ⟨θ, f θ, hν, hθ, (hf _ _).2 rfl⟩

end GlobalTheory.PowThetaFrame
