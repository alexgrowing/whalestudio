import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.HeckeSplitOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdmissibleIndexBoundAllPowers
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistModuleAllCharacterPowersOfAdmissible

open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

theorem GlobalTheory.exportAll_of_six_inputs :
    ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), admissibleIndexBoundAllPowers D.nexp (BlochKatoReduction.bk0 D) N0 → IntegralHeckeForms.IsotypicPartsInternalDirectSum D.nexp E →
      IntegralHeckeForms.GroupAlgebraIntegrality D.nexp → IntegralHeckeForms.admT4 D.nexp E → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → IntegralHeckeForms.GoodLatticePoints D.nexp →
      ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i :=
  fun D E N0 h2 h3 h5 h7 h10 h11 i hi =>
    GlobalTheory.ExportFromInputs.twistModule_all_character_powers_of_admissible D.nexp (BlochKatoReduction.bk0 D) E N0 h2 h3 h5 h7 h10 h11 i hi
