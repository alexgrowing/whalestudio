import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RhoThreeOfOfDeterminantCharacterFiniteOrderType
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MtType
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta Formalism.L2.Host GlobalTheory.KerJ NumberField Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rhoThreeOf_of_determinantCharacterFiniteOrderType : ∀ (D : D7) (u : D.what₂.Word) (C : ColumnChain D.R D.what₂.Tau (D.hcW u)) (mt : ℕ → D.Dt →* ℂˣ), MtType u mt → rhoThreeOf D C mt := by
  first | exact @GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | exact GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType | (intros; apply GlobalTheory.KerJ.RhoThree.rhoThreeOf_of_mtType <;> assumption)
