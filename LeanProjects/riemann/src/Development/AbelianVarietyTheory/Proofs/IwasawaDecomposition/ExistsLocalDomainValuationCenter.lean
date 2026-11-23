import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteIntegralClosureOfEssFiniteTypeIntDomain
open IsLocalRing GlobalTheory.Toroidal TensorProduct

namespace GlobalTheory

theorem valuativeChart_localise :
    ∀ (A B k : Type) [CommRing A] [CommRing B] [IsDomain B] [IsLocalRing B] [Algebra A B] [Field k]
      (φ : B →+* k) (V : ValuationSubring k) (C : Subalgebra A B), RingHom.ker φ = maximalIdeal B →
      Algebra.FiniteType A C → IsIntegrallyClosed C → (∀ c ∈ C, V.valuation (φ c) ≤ 1) →
      (∀ b : B, ∃ a ∈ C, ∃ s ∈ C, IsUnit s ∧ s * b = a) →
      ∃ (D : Type) (_ : CommRing D) (_ : IsDomain D) (_ : IsLocalRing D) (_ : Algebra A D) (ι : D →ₐ[A] B),
        IsIntegrallyClosed D ∧ Algebra.EssFiniteType A D ∧ Function.Injective ι ∧
        (∀ d, V.valuation (φ (ι d)) ≤ 1) ∧ (∀ d ∈ maximalIdeal D, V.valuation (φ (ι d)) < 1) ∧
        ∀ b : B, ∃ a s : D, IsUnit (ι s) ∧ ι s * b = ι a := by
  intro A B k _ _ _ _ _ _ φ V C hker hft hic hle hfrac
  let ψ : C →+* V := (φ.comp C.val.toRingHom).codRestrict V
    (fun c => (V.valuation_le_one_iff _).1 (hle c c.2))
  let p : Ideal C := (maximalIdeal V).comap ψ
  have hmem : ∀ c : C, c ∈ p ↔ V.valuation (φ c) < 1 := by
    intro c
    exact V.valuation_lt_one_iff (ψ c)
  haveI : p.IsPrime := Ideal.comap_isPrime _ _
  let D := Localization.AtPrime p
  haveI : IsDomain D := IsLocalization.isDomain_localization p.primeCompl_le_nonZeroDivisors
  have hval1 : ∀ y : p.primeCompl, V.valuation (φ (y : C)) = 1 := by
    intro y
    have h1 := hle (y : C) (y : C).2
    have h2 : ¬ V.valuation (φ (y : C)) < 1 := fun h => y.2 ((hmem _).2 h)
    exact le_antisymm h1 (not_lt.1 h2)
  have hunit : ∀ y : p.primeCompl, IsUnit (C.val (y : C)) := by
    intro y
    by_contra hnu
    have hm : ((y : C) : B) ∈ maximalIdeal B := (IsLocalRing.mem_maximalIdeal _).2 hnu
    rw [← hker, RingHom.mem_ker] at hm
    have := hval1 y
    rw [hm, map_zero] at this
    exact zero_ne_one this
  let ι : D →ₐ[A] B := IsLocalization.liftAlgHom (M := p.primeCompl) (S := D) (f := C.val) hunit
  have hιalg : ∀ c : C, ι (algebraMap C D c) = c := by
    intro c
    simp [ι, IsLocalization.liftAlgHom_apply, IsLocalization.lift_eq]
  have hrep : ∀ d : D, ∃ c : C, ∃ s : p.primeCompl, ((s : C) : B) * ι d = c ∧
      d * algebraMap C D s = algebraMap C D c := by
    intro d
    obtain ⟨⟨c, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl d
    refine ⟨c, s, ?_, IsLocalization.mk'_spec _ _ _⟩
    have := (IsLocalization.lift_mk'_spec (M := p.primeCompl) (S := D) (hg := hunit) c
      (IsLocalization.lift hunit (IsLocalization.mk' D c s)) s).1 rfl
    simpa [ι, IsLocalization.liftAlgHom_apply] using this.symm
  have hvald : ∀ d : D, ∃ c : C, V.valuation (φ (ι d)) = V.valuation (φ c) ∧
      (d ∈ maximalIdeal D → c ∈ p) := by
    intro d
    obtain ⟨c, s, h1, h2⟩ := hrep d
    refine ⟨c, ?_, ?_⟩
    · rw [← h1, map_mul, Valuation.map_mul, hval1 s, one_mul]
    · intro hd
      have : algebraMap C D c ∈ maximalIdeal D := by
        rw [← h2]; exact Ideal.mul_mem_right _ _ hd
      have h3 : c ∈ (maximalIdeal D).under C := Ideal.mem_comap.2 this
      rwa [IsLocalization.AtPrime.comap_maximalIdeal D p] at h3
  refine ⟨D, inferInstance, inferInstance, inferInstance, inferInstance, ι, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isIntegrallyClosed_of_isLocalization D p.primeCompl p.primeCompl_le_nonZeroDivisors
  · infer_instance
  · show Function.Injective (IsLocalization.lift hunit : D → B)
    rw [IsLocalization.lift_injective_iff]
    intro x y
    constructor
    · intro h
      have := congrArg (IsLocalization.lift (S := D) hunit) h
      simpa [IsLocalization.lift_eq] using this
    · intro h
      rw [Subtype.ext (show (x : B) = y from h)]
  · intro d
    obtain ⟨c, hc, -⟩ := hvald d
    rw [hc]; exact hle c c.2
  · intro d hd
    obtain ⟨c, hc, hp⟩ := hvald d
    rw [hc]; exact (hmem c).1 (hp hd)
  · intro b
    obtain ⟨a, ha, s, hs, hu, hsb⟩ := hfrac b
    refine ⟨algebraMap C D ⟨a, ha⟩, algebraMap C D ⟨s, hs⟩, ?_, ?_⟩
    · rw [hιalg]; exact hu
    · rw [hιalg, hιalg]; exact hsb

end GlobalTheory
