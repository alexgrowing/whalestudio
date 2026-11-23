import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ErrorDataGeneratorsEqColumnPreDatum
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HasPartAnd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Ker Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Fc GlobalTheory.Svd NumberField IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.errorData_generators_eq_columnPreDatum : ∀ (B : GlobalTheory.Mem.Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T) (Z : w.Lt) (t : ColT w Z), (Formalism.L2.Herm.toErrXS t.full.1).piG = w.px.piG ∧ (Formalism.L2.Herm.toErrXS t.full.1).piT = w.px.piT := by
  first | exact @GlobalTheory.Svd.errXS_pi_of_colT | exact GlobalTheory.Svd.errXS_pi_of_colT | (intros; apply GlobalTheory.Svd.errXS_pi_of_colT <;> assumption)
