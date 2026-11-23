import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjInvOfReal
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.TraceSingleMulSingle
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.IntegralTranslate
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.SquareNormIntegralNonneg
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.ConjPurelyImaginaryGenerator
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.ContinuousSplitInv
import Formalism.LocalToGlobal.IndefiniteReal.FockTheta.DeltaPf

noncomputable section

open Formalism.BasicNotions Formalism.IndefR.Fock.Sk

namespace Formalism.IndefR.Fock.Final

theorem ccrTheta_of_drho {D : D7} (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : CCRTheta D :=
  Formalism.IndefR.Fock.CCR.ccrTheta_of Formalism.IndefR.Fock.Alg.unitBracket hT hL hC

theorem fockNormO_of_drho {D : D7} (hT : ThetaDRho D) (hL : DRhoLin D) (hC : DRhoComm D) : FockNormO D :=
  Formalism.IndefR.Fock.Norm.fockNormO_of (ccrTheta_of_drho hT hL hC) Formalism.IndefR.Fock.Alg.fockNormAbs
    (Formalism.IndefR.Fock.Skew.dRhoSkew_of D hT) (Formalism.IndefR.Fock.Skew.thetaIntO D) hT

theorem fockNormO (D : D7) : FockNormO D :=
  fockNormO_of_drho (Formalism.IndefR.Fock.DRho.thetaDRho D) (Formalism.IndefR.Fock.DRho.dRhoLin D) (Formalism.IndefR.Fock.DRho.dRhoComm D)

open Formalism.IndefR.Datum in
attribute [local instance] Formalism.BasicNotions.Host.cmStar in

theorem fockNormO_lines (D : D7) :
    ∀ (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) ℂ) (θ : Formalism.IndefR.Datum.InfFam D) (S T : Formalism.BasicNotions.TH.HSp D) sS sT BS BT
      (pS pT : D.what₂.Tau → ℕ), PairSetup ψ θ S T sS sT BS BT pS pT →
    ∀ (μ : MeasureTheory.Measure (Formalism.IndefR.Datum.WO S T)) (𝓕 : Set (Formalism.IndefR.Datum.WO S T)),
      Formalism.IndefR.Datum.IsCovolOne (Formalism.L2.Theta.ratL T S) μ 𝓕 →
      ∀ f : Formalism.IndefR.Datum.WO S T → ℂ, Formalism.IndefR.Datum.IsThetaFunO ψ S T f →
        (∀ τ, Formalism.IndefR.Datum.IsFockVacAt (Formalism.IndefR.Datum.heisO ψ S T) θ τ
          (Formalism.IndefR.Datum.cplxO (sS τ) (sT τ)) f) →
        ∀ P Q : MvPolynomial (Formalism.IndefR.Datum.FVar D T.rank S.rank) ℂ,
          ∫ w in 𝓕, Formalism.IndefR.Datum.pureTensorO ψ θ S T sS sT BS BT f P w *
              starRingEnd ℂ (Formalism.IndefR.Datum.pureTensorO ψ θ S T sS sT BS BT f Q w) ∂μ =
            Formalism.REAL.fockF P Q * ∫ w in 𝓕, f w * starRingEnd ℂ (f w) ∂μ :=
  fockNormO D (Formalism.IndefR.Eqv.lineAtExists_holds D)

end Formalism.IndefR.Fock.Final

end
