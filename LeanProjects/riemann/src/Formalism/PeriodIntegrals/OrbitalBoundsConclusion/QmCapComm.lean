import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabGl
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnEabPres
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.Transfer
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.CapelliOperatorCongruence
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.QuantumDeterminantCommute.QuantumDeterminantCommutes

theorem qmCapComm_of : Formalism.FourierDecayAlt.Q.EabPres → Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  fun hP hG => QmCapCommW.capelli_operator_transfer QmCapCommW.capelli_operator_congruence QmCapCommW.quantum_determinant_commutes hP hG

theorem qmCapComm_of_gl : Formalism.FourierDecayAlt.Q.EabGlLev → Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of qnEabPres

theorem capelli_det_commute : Formalism.FourierDecayAlt.Q.CapCommute :=
  qmCapComm_of_gl qnEabGl
