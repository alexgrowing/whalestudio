import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SpecialLinearClassNumberOneAdelic
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.specialLinear_classNumber_one_adelic : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (R : Type) [CommRing R] [Algebra ℚ R] (R₀ : Subring R), AdelicPair R R₀ → ∀ x : Matrix ι ι R, x.det = 1 → ∃ (h : Matrix ι ι ℚ) (k : Matrix ι ι R), h.det = 1 ∧ k.det = 1 ∧ (∀ i j, k i j ∈ R₀) ∧ x = h.map (algebraMap ℚ R) * k := by
  first | exact @GlobalTheory.ClassFin.sl_class_number_one | exact GlobalTheory.ClassFin.sl_class_number_one | (intros; apply GlobalTheory.ClassFin.sl_class_number_one <;> assumption)
