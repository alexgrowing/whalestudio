import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryGroupPositiveCharacterTrivialAndUnimodula
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FourierMatch
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unitaryGroup_positiveCharacter_trivial_and_unimodular : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (r : ℕ), (∀ ch : Matrix.unitaryGroup (Fin r) E →* ℝ, Continuous ch → (∀ g, 0 < ch g) → ∀ g, ch g = 1) ∧ ∀ M : Meas r F E, (letI := M.mU; M.μU.IsMulRightInvariant) := by
  first | exact @GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular | exact GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular | (intros; apply GlobalTheory.JR.UnitChar.posChar_trivial_and_unimodular <;> assumption)
