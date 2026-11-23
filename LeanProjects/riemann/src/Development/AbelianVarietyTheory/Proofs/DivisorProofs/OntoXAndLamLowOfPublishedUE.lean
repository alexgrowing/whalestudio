import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.BoundAtTwoThreeFamily
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.GeometricWeakTiesOfStrong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LamLowOfPublished
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PublishedInputsImplyGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsOfHyp
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesisBundleConversions

namespace GlobalTheory.Fc.S0

theorem ontoX_and_lamLow_of_classicalTheoremsUE :
    S0.HypothesesUE → GlobalTheory.BigOn.OntoX ∧ GlobalTheory.BigTop.LamLow := by
  intro P
  exact ⟨GlobalTheory.BigOn.ontoX_of_classicalTheorems P.greenCuspidal P.clozelCohomological P.cohomologicalCsdTempered
      P.heckeLAdicCharacter P.chebotarevDegreeOne P.discreteSpectrumGL
      P.galoisRepOfPolarizedCuspidal P.baseChangeDefiniteUnitary
      P.bhattScholzeCrystallineLattices P.heckeLAdicCharacterAbove P.cuspRapidDecay
      (GlobalTheory.LocLanglandsBridge.localLanglandsGL_of_depthZero_zelevinsky_bernstein P.litN.loc.llc P.litN.loc.conv P.litN.loc.dzc
      P.litN.loc.dzi P.litN.loc.brauer P.litN.loc.chev P.globalArtinReciprocity P.litN.loc.exh
      P.litN.loc.multi P.litN.loc.cos P.litN.loc.zel P.litN.loc.geo P.litN.loc.bz)
      P.discreteSeriesCover P.casselmanWallach,
    GlobalTheory.BigTop.lamLow_of_classicalTheorems P.cuspRapidDecay P.weilSiegelFormulaUnitary
      P.siegelWeilUnitaryConvergent P.doublingMethod P.unramifiedDoublingGL
      P.bernsteinZelevinskyFiniteness P.formalDegreeCompactDual⟩

end GlobalTheory.Fc.S0
