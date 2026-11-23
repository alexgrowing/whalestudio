import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TorusInvariance.QnTInvOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnMinorLeft
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovLin
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovDet
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnCovHat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CovariantHatSqOfLin

theorem qnTInv : Formalism.FourierDecayAlt.Q.TInvariant :=
  Formalism.FourierDecayAlt.Q.TInvW.qnTInv_of
    (PI.contractionsCovariant_iff.2
      ⟨covariant_det_of_lin covariant_linear, covariant_hat_of_lin covariant_linear, covariant_hat_sq_of_lin covariant_linear⟩)
    qnEabPres qnEabGl qnMinorLeft
