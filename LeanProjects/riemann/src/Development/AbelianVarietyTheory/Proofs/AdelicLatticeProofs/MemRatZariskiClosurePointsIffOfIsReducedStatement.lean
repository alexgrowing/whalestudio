import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemRatZariskiClosurePointsIffOfIsReduced
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_ratZariskiClosurePoints_iff_of_isReduced : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (S' : Set (MvPolynomial (ι × ι) ℚ)) (R : Type) [CommRing R] [Algebra ℚ R] (y : Matrix ι ι R), (y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R → ∀ f ∈ S', ev f y = 0) ∧ (IsReduced R → (∀ f ∈ S', ev f y = 0) → y ∈ pts {g : Matrix ι ι ℂ | ∀ f ∈ S', ev f g = 0} R) := by
  first | exact @GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | exact GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced | (intros; apply GlobalTheory.ClassFin.mem_pts_zeroSet_of_isReduced <;> assumption)
