import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeadJOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActOneVariableSmul
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.WordInd
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ZOnly
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LocOfSmoothOnH

noncomputable section

namespace Formalism.FourierDecayAlt.P

theorem head_jacquet_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : LevelPointCoordinates.HeadJ :=
  LevelPointCoordinates.headJ_of (word_induction_of_parts hHL z_only rules_closed) hB

theorem radial_head_of_letter_and_head (hHL : LevelPointCoordinates.HeadLetter) (hB : LevelPointCoordinates.HeadBridge) : KB.RadHead :=
  pb_radHead_of_headJ (head_jacquet_of_letter_and_head hHL hB)

end Formalism.FourierDecayAlt.P
