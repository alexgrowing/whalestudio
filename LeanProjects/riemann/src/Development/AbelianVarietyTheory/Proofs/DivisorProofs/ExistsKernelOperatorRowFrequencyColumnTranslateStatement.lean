import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKernelOperatorRowFrequencyColumnTranslate
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OnMatInfOfIsUnit
open NumberField GlobalTheory.CuspRep GlobalTheory.JSW GlobalTheory.JSW.MirCinf MeasureTheory
open scoped FourierTransform ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kernelOperator_rowFrequency_columnTranslate : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (ρ : Fin n), (ρ : ℕ) + 1 < n → ∀ (Z : Type) [NormedAddCommGroup Z] [NormedSpace ℝ Z] [FiniteDimensional ℝ Z] (T : (GL (Fin n) (Cinf E) → ℂ) → Z × (Fin n → Cinf E) → GL (Fin n) (Cinf E) → ℂ), IsKerOpInf T → ∃ T' : (GL (Fin n) (Cinf E) → ℂ) → Z → GL (Fin n) (Cinf E) → ℂ, IsKerOpInf T' ∧ ∀ W, IsModGrowthInf W → IsWhitInf W → ∀ z, ∀ g ∈ levSetInf E n (ρ + 1), T' W z g = T W (z, rowCutInf ρ (g : Matrix (Fin n) (Fin n) (Cinf E))) g := by
  first | exact @GlobalTheory.JSW.MirCinf.exists_kerOpInf_rowFreq_colGL | exact GlobalTheory.JSW.MirCinf.exists_kerOpInf_rowFreq_colGL | (intros; apply GlobalTheory.JSW.MirCinf.exists_kerOpInf_rowFreq_colGL <;> assumption)
