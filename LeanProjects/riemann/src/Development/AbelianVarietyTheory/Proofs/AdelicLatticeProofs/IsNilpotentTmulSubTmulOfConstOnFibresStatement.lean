import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsNilpotentTmulSubTmulOfConstOnFibres
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isNilpotent_tmul_sub_tmul_of_const_on_fibres' : ∀ (B A : Type) [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A] [Algebra B A] [IsScalarTower ℂ B A] [Algebra.FiniteType ℂ A] (f : A), (∀ χ χ' : A →ₐ[ℂ] ℂ, (∀ b : B, χ (algebraMap B A b) = χ' (algebraMap B A b)) → χ f = χ' f) → IsNilpotent (f ⊗ₜ[B] (1 : A) - (1 : A) ⊗ₜ[B] f) := by
  first | exact @GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres | exact GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres | (intros; apply GlobalTheory.ClassFin.isNilpotent_tmul_sub_tmul_of_const_on_fibres <;> assumption)
