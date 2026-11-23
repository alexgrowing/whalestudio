import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderES
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmBorderFull
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmMove
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmSandwich
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevBasics
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnGlevImage
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnLevTransfer
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleLeft
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnRuleTorus
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTInv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnTPres
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QmCapComm
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnHermHaar
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QnWCell

theorem Formalism.FourierDecayAlt.P.border_first_expansion : Formalism.FourierDecayAlt.Q.BorderE := by
  exact quantum_minor_border_es.1

theorem Formalism.FourierDecayAlt.P.border_last_expansion : Formalism.FourierDecayAlt.Q.BorderS := by
  exact quantum_minor_border_es.2

theorem Formalism.FourierDecayAlt.P.border_full_expansion : Formalism.FourierDecayAlt.Q.BorderFull := by
  exact quantum_minor_border_full

theorem Formalism.FourierDecayAlt.P.move_vector_identity : Formalism.FourierDecayAlt.Q.MoveVec := by
  exact quantum_minor_move.1

theorem Formalism.FourierDecayAlt.P.move_covariance : Formalism.FourierDecayAlt.Q.MoveCov := by
  exact quantum_minor_move.2

theorem Formalism.FourierDecayAlt.P.rtt_sandwich : Formalism.FourierDecayAlt.Q.RTTSandwich := by
  exact rtt_sandwich'

theorem Formalism.FourierDecayAlt.P.level_group_image : Formalism.FourierDecayAlt.Q.GlevImage := by
  obtain ⟨hH, hU, -⟩ := level_basics
  exact gl_level_image hH hU

theorem Formalism.FourierDecayAlt.P.level_transfer : Formalism.FourierDecayAlt.Q.LevelTransfer := by
  exact level_transfer_of_levHom level_basics.1

theorem Formalism.FourierDecayAlt.P.left_action_rule : Formalism.FourierDecayAlt.Q.RuleLeft := by
  exact qnRuleLeft

theorem Formalism.FourierDecayAlt.P.torus_action_rule : Formalism.FourierDecayAlt.Q.RuleTorus := by
  exact qnRuleTorus

theorem Formalism.FourierDecayAlt.P.operator_invariance : Formalism.FourierDecayAlt.Q.TInvariant := by
  exact qnTInv

theorem Formalism.FourierDecayAlt.P.operator_preserves_fusion_forms : Formalism.FourierDecayAlt.Q.TPreservesFF := by
  exact qnTPres

theorem Formalism.FourierDecayAlt.P.capelli_commutation : Formalism.FourierDecayAlt.Q.CapCommute := by
  exact capelli_det_commute

theorem Formalism.FourierDecayAlt.P.hermitian_haar_invariance : Formalism.FourierDecayAlt.Q.HermHaar := by
  exact qnHermHaar

theorem Formalism.FourierDecayAlt.P.hermitian_from_algebra : Formalism.FourierDecayAlt.Q.HermFromSteps := by
  intro _ _ _ _ _ _ _ _
  exact qnHermHaar

theorem Formalism.FourierDecayAlt.P.weyl_cell_big_cell : Formalism.FourierDecayAlt.Q.WCellBigCell := by
  exact quantum_w_big_cell
