import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalDomainValuationDominated
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open IsLocalRing GlobalTheory.Toroidal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_domain_valuation_dominated : ∀ (A B k : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k), RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) → (∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  first | exact @GlobalTheory.exists_normal_localization_chart_centred | exact GlobalTheory.exists_normal_localization_chart_centred | (intros; apply GlobalTheory.exists_normal_localization_chart_centred <;> assumption)
