import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTA
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsKMOne
open NumberField Matrix GlobalTheory.AdLat GlobalTheory.UCls
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isTA_conj_det_of_isUA_cm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), G.det ≠ 0 → IsUA (IsCMField.complexConj E) G g → IsTA (IsCMField.complexConj E) g.det := by
  first | exact @GlobalTheory.unitary_det_isTA | exact GlobalTheory.unitary_det_isTA | (intros; apply GlobalTheory.unitary_det_isTA <;> assumption)
