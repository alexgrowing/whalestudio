import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalParameterLawsOfWeilDeligneIdentification
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localParameterLaws_of_weilDeligneIdentification : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N), GlobalTheory.RowTie.WDTie N A → GlobalTheory.ThetaExh.ParamLaws N A ∧ GlobalTheory.RowTie.CharLaws N A ∧ GlobalTheory.RowTie.Cancel N A := by
  first | exact @GlobalTheory.RowLaws.main | exact GlobalTheory.RowLaws.main | (intros; apply GlobalTheory.RowLaws.main <;> assumption)
