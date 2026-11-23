import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselModelUnitaryGroupOpNormProperties
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.besselModelUnitaryGroup_opNorm_properties : ∀ (k r : ℕ) , (∀ g ∈ GG k r, opn g⁻¹ = opn g ∧ 1 ≤ opn g) ∧ (∀ x y : Mat k r, opn (x * y) ≤ opn x * opn y) ∧ Continuous (fun x : Mat k r => opn x) ∧ (∀ (x : Mat k r) i j, ‖x i j‖ ≤ opn x) ∧ (∀ (x : Mat k r) (v : Fin (2 * r + k + 1) → ℂ), eucl (x *ᵥ v) ≤ opn x * eucl v) ∧ (∀ u v : Fin (2 * r + k + 1) → ℂ, ‖herm (Hpk k r) u v‖ ≤ eucl u * eucl v) ∧ (∀ x ∈ GG k r, ∀ y ∈ GG k r, opn x / opn y ≤ opn (x * y) ∧ opn y / opn x ≤ opn (x * y)) ∧ (∀ x : Mat k r, opn x ≤ Real.sqrt (Formalism.REAL.hs x) ∧ Real.sqrt (Formalism.REAL.hs x) ≤ ((2 * r + k + 1 : ℕ) : ℝ) * opn x) := by
  first | exact @GlobalTheory.SgInf.opn_facts | exact GlobalTheory.SgInf.opn_facts | (intros; apply GlobalTheory.SgInf.opn_facts <;> assumption)
