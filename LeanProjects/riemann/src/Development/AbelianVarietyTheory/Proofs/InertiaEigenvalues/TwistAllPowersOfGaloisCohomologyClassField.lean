import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNineTermTransgressionZeroApply
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.CohDimTwoLocalOfLocalFiniteness
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ContinuousCycMod
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ExistsIdealsPrimeToEqSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnivCharWithUnivChar
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistTheoremAllPowersOfSelmerSupLattice
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NotValuationNatCastLtOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualityDimOfLocalTheorem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ResidualSelmerBoundOfAuxiliaryPrimesOddStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundModTwoUniformizerAtTwoOfChebotarevStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SelmerPresentationMatrixOfGaloisCohomologyStatement
open GlobalTheory.LiftLeaf GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw Formalism.BasicNotions Formalism.MainNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.Published

namespace GlobalTheory.TwExportTop

theorem twistAllPowers_of_galoisCohomology_classField :
    Cheb → PoitouTateTotallyComplex → CohDimTwo → TameLocal → LocalFiniteness → LocalTateDuality → LocalEulerChar → GlobalFiniteness → GlobalEulerChar → UnramifiedOrthogonality → BlochKatoReduction.Gen.ArchimedeanSignatureMatching → GreenbergWiles → RayCharacterArtin → ∀ (D : D7) (E : IntegralHeckeForms.XD D) (N0 : D.ntw.Tw → ℕ), LocalSituation.Conclusion5 D → BlochKatoReduction.adm1 (BlochKatoReduction.bk0 D) → BlochKatoReduction.adm2 D → BlochKatoReduction.adm8 D → AllGood D.nexp → D.nexp.sig_all → BlochKatoReduction.adm9 D N0 → BlochKatoReduction.adm10 D → GlobalTheory.UnivChar.IsUnivChar D.nexp → OffRange D → ThURel D.nexp → IntegralHeckeForms.TwistedSeriesSpecialisation D.nexp → IntegralHeckeForms.admT4 D.nexp E → TypeKept E → UnivSup D E → SupG D → SupFull D → SupHk D → CommG D → HkComm D → HkSS D → ∀ i, D.ntw.NonzeroIndexPlace i → goodTwistExistsAllCoprimePowers D.nexp (BlochKatoReduction.bk0 D) E N0 i := by
  intro hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW hRC D E N0 h5 h1 h2 h8 hGood hSig h9 h10 hUniv hOff hRel
    hL3 hT4 hT hU hG hFull hHk hComm hHC hSS
  exact GlobalTheory.TwExportSup.twistTheorem_allPowers_of_selmer_supLattice D E N0
    (GlobalTheory.T.selmerPresentationMatrix_of_galois_cohomology hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 D D.nd D.ntw (BlochKatoReduction.bk0 D))
    (GlobalTheory.T.residualSelmerBound_of_auxiliaryPrimes_odd hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 hGW D D.nd D.ntw (BlochKatoReduction.bk0 D))
    (GlobalTheory.T.boundModTwoUniformizerAtTwo_of_chebotarev hCh hPT hCD hTL hLF hLT hLE hGF hGE hUO h4 D D.nd D.ntw (BlochKatoReduction.bk0 D))
    ⟨h1, h2, (GlobalTheory.BlochKato₂.duality_dim_of_localTheorem D h5).1, h4, h9, h10⟩
    (GlobalTheory.UnivChar.delUTie_of_isUnivChar D.nexp (GlobalTheory.AdmChars.exists_admissible_family D.ntw hRC) hUniv)
    hRel hHC hOff hGood h8 hG hFull hHk hU hT hComm hT4 hL3 hSig hSS

end GlobalTheory.TwExportTop
