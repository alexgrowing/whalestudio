import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2

section
namespace GlobalTheory.CovTop
structure PublishedHodgeBundleTheorems : Prop where
  p1 : GlobalTheory.Published.ToroidalCompactification
  p2 : GlobalTheory.Published.VolGe
  p3 : GlobalTheory.Published.VolNef
  p4 : GlobalTheory.Published.ArCalc
  p5 : GlobalTheory.Published.AbelianDeRham
  p8 : GlobalTheory.Published.RayClassFieldSt
  p12 : GlobalTheory.Published.SemistableReductionSt
  p13 : GlobalTheory.Published.StrongApproxSU
  p14 : GlobalTheory.Published.GreenSeriesSt
  p16 : GlobalTheory.Published.GoodChernWeil
  p19 : GlobalTheory.Published.LandherrSt
  p20 : GlobalTheory.Published.HasseNormSt
  p22 : GlobalTheory.Published.SemiAbelianHomExtension
  p23 : GlobalTheory.Published.InducedSimpleLowestAlcove
  p25 : GlobalTheory.Published.principalPolarisationOneSection
  p26 : GlobalTheory.Published.AbMulNSt
  q1 : GlobalTheory.Published.GrothendieckMessing
  q4 : GlobalTheory.Published.PrismaticDieudonneHodge
  q6 : GlobalTheory.Published.KawamataViehweg
  q7 : GlobalTheory.Published.NefNumerics
  q8 : GlobalTheory.Published.L2ExtensionLogCanonical
  q9 : GlobalTheory.Published.ArithHilbertSamuel
  q10 : GlobalTheory.Published.ChowFormExists
  q11 : GlobalTheory.Published.CycleHeights
  q13 : GlobalTheory.Published.SerreHolomorphicSections
  q15 : GlobalTheory.Published.NadelVanishingAndNonKltDivisor
  q16 : GlobalTheory.Published.Principalisation
  q18 : GlobalTheory.Published.FormalAlgebraisation
theorem PublishedHodgeBundleTheorems.p18 (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : GlobalTheory.Published.FinitenessOfHermitianClasses := GlobalTheory.Published.finitenessOfHermitianClasses_holds
theorem PublishedHodgeBundleTheorems.q2 (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : GlobalTheory.Published.CanonicalExtensionRankOne := GlobalTheory.Published.canonicalExtensionRankOne_holds
theorem PublishedHodgeBundleTheorems.q12 (_h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) : GlobalTheory.Published.ProperIntersectionLength := GlobalTheory.Published.ProperIntersectionLength_holds
theorem PublishedHodgeBundleTheorems.toClassicalTheoremsOf (h : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hM : GlobalTheory.Published.GoodChernWeil → GlobalTheory.Published.MumfordProportionality) : _root_.GlobalTheory.CovTop.Hypotheses'' := by
  have hM' := hM h.p16
  refine ⟨h.p1, h.p2, h.p3, h.p4, h.p5, h.p8, h.p12, h.p13, h.p14, ?_,
    h.p18, h.p19, h.p20, h.p22, h.p23, h.p25, h.p26⟩
  first
    | exact h.p16
    | exact hM'
end GlobalTheory.CovTop
end
