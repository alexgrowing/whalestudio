import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaKEqNegOneOfNotNorm
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitting
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaK_eq_neg_one_of_not_norm : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∀ s : A.Kˣ, (¬ ∃ y : A.L, A.NL y = s) → A.etaK s = -1 := by
  first | exact @GlobalTheory.JR.NonNorm.etaK_eq_neg_one | exact GlobalTheory.JR.NonNorm.etaK_eq_neg_one | (intros; apply GlobalTheory.JR.NonNorm.etaK_eq_neg_one <;> assumption)
