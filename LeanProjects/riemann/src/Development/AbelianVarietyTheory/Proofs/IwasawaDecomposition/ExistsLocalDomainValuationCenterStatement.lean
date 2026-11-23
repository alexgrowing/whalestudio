import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalDomainValuationCenter
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_domain_valuation_center : ∀ (A B k : Type) [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Field k] (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), RingHom.ker φ = maximalIdeal B → Algebra.FiniteType A C → IsIntegrallyClosed C → (∀ c ∈ C, V.valuation (φ c) ≤ 1) → (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  first | exact @GlobalTheory.valuativeChart_localise | exact GlobalTheory.valuativeChart_localise | (intros; apply GlobalTheory.valuativeChart_localise <;> assumption)
