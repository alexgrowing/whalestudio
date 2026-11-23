import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CentralEig2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LevEraseLe
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.PRep Formalism.L2.Host GlobalTheory.HeckeGal UpperTheory.Gal.CertificateRingHomMap
open GlobalTheory.LFun (KGL)
open GlobalTheory.CongL (SatU)
open GlobalTheory.Cong (Apart)
open scoped Classical

namespace UpperTheory.Gal.CertificateRingHomMap

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

end UpperTheory.Gal.CertificateRingHomMap

theorem UpperTheory.Gal.CertificateRingHomMap.pVecU_of :
    UpperTheory.Gal.CertificateRingHomMap.NbhdU → UpperTheory.Gal.CertificateRingHomMap.StepAt → UpperTheory.Gal.CertificateRingHomMap.SphType → UpperTheory.Gal.CertificateRingHomMap.LocComm → UpperTheory.Gal.CertificateRingHomMap.VecU :=
  _root_.UpperTheory.Reformulated.B.Grk2.pVecU_of
