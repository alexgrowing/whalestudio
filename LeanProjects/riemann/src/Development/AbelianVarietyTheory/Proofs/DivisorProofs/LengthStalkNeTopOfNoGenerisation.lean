import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory

namespace GlobalTheory

theorem isFiniteLength_localized_of_minimal_prime {A B M N : Type*} [CommRing A] [CommRing B]
    [IsNoetherianRing A] [Algebra A B] (p : Ideal A) [p.IsPrime] [IsLocalization.AtPrime B p]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] (f : M →ₗ[A] N) [IsLocalizedModule p.primeCompl f]
    (h : ∀ q : Ideal A, q.IsPrime → Module.annihilator A M ≤ q → q ≤ p → q = p) :
    IsFiniteLength B N := by
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing p.primeCompl B inferInstance
  have : Module.Finite B N := Module.Finite.of_isLocalizedModule p.primeCompl f
  have : IsLocalRing B := IsLocalization.AtPrime.isLocalRing B p
  have : IsArtinianRing (B ⧸ Module.annihilator B N) := by
    rw [isArtinianRing_iff_isNoetherianRing_krullDimLE_zero]
    refine ⟨inferInstance, Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_⟩
    let Q' := Q.comap (Ideal.Quotient.mk (Module.annihilator B N))
    have hQ' : Q'.IsPrime := Ideal.comap_isPrime _ _
    have h1 : Module.annihilator A M ≤ Q'.comap (algebraMap A B) := by
      intro a ha
      have : algebraMap A B a ∈ Module.annihilator B N := by
        rw [← map_annihilator_of_isLocalizedModule p.primeCompl f]
        exact Ideal.mem_map_of_mem _ ha
      simp only [Q', Ideal.mem_comap]
      rw [Ideal.Quotient.eq_zero_iff_mem.2 this]
      exact Q.zero_mem
    have h2 : Q'.comap (algebraMap A B) ≤ p := by
      rw [← IsLocalization.AtPrime.comap_maximalIdeal B p]
      exact Ideal.comap_mono (IsLocalRing.le_maximalIdeal hQ'.ne_top)
    have h3 : Ideal.under A Q' = p := h _ (Ideal.comap_isPrime _ _) h1 h2
    have h4 : Q' = IsLocalRing.maximalIdeal B := by
      rw [← IsLocalization.map_comap p.primeCompl B Q', h3,
        IsLocalization.AtPrime.map_eq_maximalIdeal]
    have h5 : Q'.IsMaximal := h4 ▸ IsLocalRing.maximalIdeal.isMaximal B
    have h6 := Ideal.map_eq_top_or_isMaximal_of_surjective
      (Ideal.Quotient.mk (Module.annihilator B N)) Ideal.Quotient.mk_surjective h5
    rw [Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at h6
    exact h6.resolve_left hQ.ne_top
  exact isFiniteLength_of_isArtinianRing_annihilator

theorem QCoh.length_stalk_ne_top_of_no_generisation (X : Scheme.{0}) [IsLocallyNoetherian X]
    (F : X.Modules) [GlobalTheory.QCoh.IsFiniteQC F] (w : X)
    (h : ∀ y ∈ GlobalTheory.QCoh.support F, w ∈ closure ({y} : Set X) → y = w) :
    Module.length (X.presheaf.stalk w) (F.presheaf.stalk w :) ≠ ⊤ := by
  obtain ⟨U, hU, hx⟩ := QCoh.exists_affine_mem w
  obtain ⟨x, rfl⟩ : ∃ x' : U, x' = w := ⟨⟨w, hx⟩, rfl⟩
  have := hU.isLocalization_stalk x
  have := QCoh.isLocalizedModule_germLinear F hU x
  have := QCoh.finite_sections F hU
  have : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  rw [Module.length_ne_top_iff]
  refine isFiniteLength_localized_of_minimal_prime (hU.primeIdealOf x).asIdeal
    (QCoh.germLinear F x) fun q hq h1 h2 => ?_
  let P : PrimeSpectrum Γ(X, U) := ⟨q, hq⟩
  have hP : hU.fromSpec P ∈ QCoh.support F := by
    have : P ∈ Module.support Γ(X, U) Γ(F, U) := Module.mem_support_iff_of_finite.2 h1
    rw [← QCoh.fromSpec_preimage_support F hU] at this
    exact this
  have hs : P ⤳ hU.primeIdealOf x := (PrimeSpectrum.le_iff_specializes _ _).1 h2
  have hs' : hU.fromSpec P ⤳ (x : X) := by
    rw [← hU.fromSpec_primeIdealOf x]
    exact hs.map hU.fromSpec.continuous
  have e := h _ hP (specializes_iff_mem_closure.1 hs')
  rw [← hU.fromSpec_primeIdealOf x] at e
  have e' : P = hU.primeIdealOf x := hU.fromSpec.isOpenEmbedding.injective e
  exact congrArg PrimeSpectrum.asIdeal e'

end GlobalTheory
