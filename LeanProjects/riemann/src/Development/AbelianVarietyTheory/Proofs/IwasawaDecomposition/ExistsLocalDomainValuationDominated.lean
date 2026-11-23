import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteTypeValuationCenterStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalFiniteTypeOverStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalDomainValuationCenterStatement
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem valuation_le_one_of_isIntegral_subalgebra : ∀ (A B k : Type) [CommRing A] [CommRing B] [Algebra A B] [Field k] (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), (∀ c ∈ C, V.valuation (φ c) ≤ 1) → ∀ x : B, IsIntegral C x → V.valuation (φ x) ≤ 1 := by
  intro A B k _ _ _ _ φ V C hC x hx
  let ψ : C →+* V := (φ.comp C.val.toRingHom).codRestrict V.toSubring (fun c => (V.valuation_le_one_iff _).mp (hC c c.2))
  have h := IsIntegral.map_of_comp_eq ψ φ (by ext c; rfl) hx
  have h2 : φ x ∈ V := by
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp h
    rw [← hy]; exact y.2
  exact (V.valuation_le_one_iff _).mpr h2

theorem exists_normal_localization_chart_centred : ∀ (A B k : Type) [CommRing A] [IsLocalRing A] [Algebra.EssFiniteType ℤ A] [CommRing B] [IsDomain B] [IsLocalRing B] [IsIntegrallyClosed B] [Algebra A B] [Algebra.EssFiniteType A B] [Field k] (φ : B →+* k) (V : ValuationSubring k), RingHom.ker φ = maximalIdeal B → (∀ a : A, V.valuation (φ (algebraMap A B a)) ≤ 1) → (∀ a ∈ maximalIdeal A, V.valuation (φ (algebraMap A B a)) < 1) → ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B), IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧ (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧ ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  intro A B k _ _ _ _ _ _ _ _ _ _ φ V hker hA _
  obtain ⟨C, hCft, hCv, hCfrac⟩ := GlobalTheory.T.exists_finite_type_valuation_center A B k φ V hker hA
  obtain ⟨C', hle, hft', hic', hint⟩ := GlobalTheory.T.exists_normal_finite_type_over A B C hCft (fun b => by
    obtain ⟨a, ha, s, hs, hu, he⟩ := hCfrac b
    exact ⟨a, ha, s, hs, hu.ne_zero, he⟩)
  have hv' : ∀ c ∈ C', V.valuation (φ c) ≤ 1 := fun c hc =>
    valuation_le_one_of_isIntegral_subalgebra A B k φ V C hCv c (hint c hc)
  exact GlobalTheory.T.exists_local_domain_valuation_center A B k φ V C' hker hft' hic' hv' (fun b => by
    obtain ⟨a, ha, s, hs, hu, he⟩ := hCfrac b
    exact ⟨a, hle ha, s, hle hs, hu, he⟩)

end GlobalTheory
