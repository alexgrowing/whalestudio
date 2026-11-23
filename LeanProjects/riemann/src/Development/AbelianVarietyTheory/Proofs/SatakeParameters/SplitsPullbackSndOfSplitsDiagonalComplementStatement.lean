import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitsPullbackSndOfSplitsDiagonalComplement
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FibrePointsLEId
open CategoryTheory Limits AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.splits_pullbackSnd_of_splits_diagonalComplement : ∀ {Z X V : Scheme.{0}} (f : Z ⟶ X) [IsFinite f] [Etale f] (v : V ⟶ Z), GlobalTheory.EtC.Tr.Splits (GlobalTheory.EtC.Tr.diagComplHom f) v → GlobalTheory.EtC.Tr.Splits (pullback.snd f f) v := by
  first | exact @GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom | exact GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom | (intros; apply GlobalTheory.EtC.Tr.splits_pullbackSnd_of_splits_diagComplHom <;> assumption)
