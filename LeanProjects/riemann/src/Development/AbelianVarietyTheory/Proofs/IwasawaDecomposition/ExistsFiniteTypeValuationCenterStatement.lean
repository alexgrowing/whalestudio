import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteTypeValuationCenter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_type_valuation_center : ∀ (A B k : Type) [CommRing A] [CommRing B] [IsLocalRing B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k), RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) → ∃ C : Subalgebra A B, Algebra.FiniteType A C ∧ (∀ c ∈ C, V.valuation (φ c) ≤ 1) ∧ ∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a := by
  first | exact @GlobalTheory.valuativeChart_exists_fg_subalgebra | exact GlobalTheory.valuativeChart_exists_fg_subalgebra | (intros; apply GlobalTheory.valuativeChart_exists_fg_subalgebra <;> assumption)
