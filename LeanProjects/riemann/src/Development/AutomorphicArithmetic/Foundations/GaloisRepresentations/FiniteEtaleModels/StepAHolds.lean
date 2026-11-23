import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.StepAOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.CoreAOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ADictP
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ASysExt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrEtaK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.AGalOfKer
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrPull
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ATrSame
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevTr
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ALevRe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaH
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ABetaLat
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.ANumSplit

open UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.FiniteEtaleModels

theorem stepA_holds (h₁ : MultUnit) (h₂ : LatGen) (h₃ : ClsEx) (h₄ : TrEta) (h₅ : TrBack) (h₆ : QComp) : StepA :=
  stepA_of (dictP_holds h₁) sysExt_holds trEtaK_holds trKer_holds galOfKer_holds betaH_holds (betaLat_holds h₂) numSplit_holds
    (coreA_of trPull trSame_holds levTr_holds levRe_holds h₃) h₄ h₅ h₆

end UpperTheory.Gal.FiniteEtaleModels
