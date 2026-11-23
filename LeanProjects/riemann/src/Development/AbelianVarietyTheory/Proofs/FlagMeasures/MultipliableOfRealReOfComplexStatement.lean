import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MultipliableOfRealReOfComplex
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multipliable_ofReal_re_of_nonneg_real : ∀ (ι : Type) (c : ι → ℂ), Multipliable c → (∀ i, (c i).im = 0 ∧ 0 ≤ (c i).re) → Multipliable (fun i => ENNReal.ofReal (c i).re) ∧ ∏' i, ENNReal.ofReal (c i).re = ENNReal.ofReal (∏' i, c i).re := by
  first | exact @GlobalTheory.multipliable_ofReal_re_of_complex' | exact GlobalTheory.multipliable_ofReal_re_of_complex' | (intros; apply GlobalTheory.multipliable_ofReal_re_of_complex' <;> assumption)
