import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweDualityUpwardOfLocalThetaSplitPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.howeDualityUpward_of_localThetaSplitPlaces : ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N) (i : N.Loc), GlobalTheory.RowTie.PairLift N A i → GlobalTheory.RowTie.BCEx N A i → GlobalTheory.RowTie.SplitBC N A i → GlobalTheory.RowTie.RepOfLoc N A i → GlobalTheory.ThetaExh.HoweUp N A i := by
  first | exact @GlobalTheory.RowTie.howeUp_of_pairLift | exact GlobalTheory.RowTie.howeUp_of_pairLift | (intros; apply GlobalTheory.RowTie.howeUp_of_pairLift <;> assumption)
