import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquarefreeMonicPolyLabelsSemisimpleParameter
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squarefree_monic_poly_labels_semisimple_parameter : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (f : (ZMod p)[X]), f.Monic → f.natDegree = r → f.coeff 0 ≠ 0 → Squarefree f → ∃ (s : SSParam p ℂ r) (x : Cyc s.1 → Fbar p), Labels L s x f := by
  first | exact @GlobalTheory.ParamExists.param_exists | exact GlobalTheory.ParamExists.param_exists | (intros; apply GlobalTheory.ParamExists.param_exists <;> assumption)
