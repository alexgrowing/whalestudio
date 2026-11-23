import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.NhdsBasisLevelSubgroup
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.PVecWt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PThLoc
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrRho
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTrSch
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PSchHom
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCharConj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtCore
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PAutEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PWtAtOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PEpsIff
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpSum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PExpCore

namespace UpperTheory.Gal.CertificateRingHomMap

theorem trRho_holds : TrRho := pTrRho_of
theorem trSch_holds : TrSch := pTrSch_of
theorem schHom_holds : SchHom := pSchHom_of
theorem charConj_holds : CharConj := pCharConj_of
theorem wtCore_holds : WtCore := pWtCore_of trRho_holds trSch_holds schHom_holds charConj_holds
theorem autEx_holds : AutEx := pAutEx_of
theorem wtAt_holds : WtAt := pWtAt_of
theorem epsIff_holds : EpsIff := pEpsIff_of
theorem expSum_holds : ExpSum := pExpSum_of
theorem expCore_holds : ExpCore := pExpCore_of expSum_holds

end UpperTheory.Gal.CertificateRingHomMap

namespace UpperTheory.Gal.Int.Geo.Pl

theorem vecEx_holds : VecEx := vecEx_of CertificateRingHomMap.seedGU_holds CertificateRingHomMap.wtAt_holds

theorem wtOf_holds : WtOf := wtOf_of CertificateRingHomMap.wtCore_holds

theorem expOf_holds : ExpOf := expOf_of CertificateRingHomMap.expCore_holds CertificateRingHomMap.autEx_holds CertificateRingHomMap.wtAt_holds CertificateRingHomMap.epsIff_holds

end UpperTheory.Gal.Int.Geo.Pl
