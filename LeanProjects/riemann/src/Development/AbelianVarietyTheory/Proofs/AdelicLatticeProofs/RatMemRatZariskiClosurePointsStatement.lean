import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RatMemRatZariskiClosurePoints
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rat_mem_ratZariskiClosurePoints : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)), (∀ γ : Matrix ι ι ℚ, γ.map (algebraMap ℚ ℂ) ∈ Γ → γ ∈ pts Γ ℚ) ∧ ∀ (R : Type) [CommRing R] [Algebra ℚ R], ∀ γ ∈ pts Γ ℚ, γ.map (algebraMap ℚ R) ∈ pts Γ R := by
  first | exact @GlobalTheory.ClassFin.RatPts.rat_mem_pts | exact GlobalTheory.ClassFin.RatPts.rat_mem_pts | (intros; apply GlobalTheory.ClassFin.RatPts.rat_mem_pts <;> assumption)
