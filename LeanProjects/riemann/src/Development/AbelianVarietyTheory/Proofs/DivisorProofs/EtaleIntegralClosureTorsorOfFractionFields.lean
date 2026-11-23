import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapMaximalIdealEqOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodIffEtaleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraMapTmulOne

open IsLocalRing Polynomial
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KeyOriginTransport

open GlobalTheory.KeyOriginBC

theorem etale_closure_of_field : (∀ (S S₁ K K₁ : Type) [CommRing S] [IsDomain S] [IsDiscreteValuationRing S] [CommRing S₁]
    [IsDomain S₁] [IsDiscreteValuationRing S₁] [Field K] [Algebra S K] [IsFractionRing S K] [Field K₁]
    [Algebra S₁ K₁] [IsFractionRing S₁ K₁] [Algebra S S₁] [Algebra K K₁] [Algebra S K₁]
    [IsScalarTower S K K₁] [IsScalarTower S S₁ K₁],
    Function.Injective (algebraMap S S₁) → ∀ (q : ℕ), 0 < q → IsUnit (q : S) →
    ∀ π : S, Irreducible π → ∀ y : S₁, y ^ q = algebraMap S S₁ π →
    ∀ (M : Type) [CommRing M] [Algebra K M] (act : Multiplicative (ZMod q) →* (M ≃ₐ[K] M)),
    GlobalTheory.KeyOriginCut.IsZTorsor K M q act →
    Algebra.Etale S₁ (integralClosure S₁ (K₁ ⊗[K] M))) →
  ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [Algebra A R],
    Function.Injective (algebraMap A R) →
    ∀ (A₁ R₁ : Type) [CommRing A₁] [IsDomain A₁] [CommRing R₁] [IsDomain R₁] [Algebra A₁ R₁],
    Function.Injective (algebraMap A₁ R₁) →
    ∀ (f : A →+* A₁), Function.Injective f → ∀ (φ : R →+* R₁),
    φ.comp (algebraMap A R) = (algebraMap A₁ R₁).comp f →
    ∀ (β : GlobalTheory.LocAcyc.GenFib A R →+* GlobalTheory.LocAcyc.GenFib A₁ R₁),
    β.comp (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) =
      (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁)).comp φ →
    ∀ (DA : Type) [CommRing DA] [Algebra (GlobalTheory.LocAcyc.GenFib A R) DA] (q : ℕ)
      (act : Multiplicative (ZMod q) →* (DA ≃ₐ[GlobalTheory.LocAcyc.GenFib A R] DA)),
    0 < q → IsUnit (q : A) → GlobalTheory.KeyOriginCut.IsZTorsor (GlobalTheory.LocAcyc.GenFib A R) DA q act →
    ∀ (P₁ : Ideal R₁) [P₁.IsPrime],
    IsDiscreteValuationRing (Localization.AtPrime P₁) →
    IsDiscreteValuationRing (Localization.AtPrime (P₁.comap φ)) →
    ∀ π : A, Irreducible (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) →
    ∀ y : R₁, y ^ q = φ (algebraMap A R π) →
    (letI := (GlobalTheory.KeyOriginNoeth.baseHom A₁ R₁ (GlobalTheory.KeyOriginBC.BC β DA)).toAlgebra;
      Algebra.Etale (Localization.AtPrime P₁)
        (integralClosure (Localization.AtPrime P₁) (Localization.AtPrime P₁ ⊗[R₁] GlobalTheory.KeyOriginBC.BC β DA))) := by
  intro H A R _ _ _ _ _ hAR A₁ R₁ _ _ _ _ _ hAR₁ f hf φ hφ β hβ DA _ _ q act hq hqA htor P₁ _ hS₁ hS π hπ y hy
  haveI := hS₁
  haveI := hS
  letI algSS₁ : Algebra (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) :=
    (Localization.localRingHom (P₁.comap φ) P₁ φ rfl).toAlgebra
  have hloc : ∀ r : R, algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
      (algebraMap R (Localization.AtPrime (P₁.comap φ)) r) = algebraMap R₁ (Localization.AtPrime P₁) (φ r) :=
    Localization.localRingHom_to_map _ _ _ rfl
  have hR₁S₁ : Function.Injective (algebraMap R₁ (Localization.AtPrime P₁)) :=
    IsLocalization.injective _ P₁.primeCompl_le_nonZeroDivisors
  have hRS : Function.Injective (algebraMap R (Localization.AtPrime (P₁.comap φ))) :=
    IsLocalization.injective _ (P₁.comap φ).primeCompl_le_nonZeroDivisors
  have hπS : algebraMap A (Localization.AtPrime (P₁.comap φ)) π =
      algebraMap R (Localization.AtPrime (P₁.comap φ)) (algebraMap A R π) :=
    IsScalarTower.algebraMap_apply A R _ π
  have hφw : φ (algebraMap A R π) = algebraMap A₁ R₁ (f π) := by
    rw [← RingHom.comp_apply, hφ]; rfl
  have hπ0 : f π ≠ 0 := by
    intro h
    apply hπ.ne_zero
    have h0 : π = 0 := (injective_iff_map_eq_zero f).1 hf π h
    rw [h0, map_zero]
  have hx0 : algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π)) ≠ 0 := by
    rw [hφw]
    intro h
    exact hπ0 ((injective_iff_map_eq_zero _).1 hAR₁ _ ((injective_iff_map_eq_zero _).1 hR₁S₁ _ h))
  have hxu : ¬ IsUnit (algebraMap R₁ (Localization.AtPrime P₁) (φ (algebraMap A R π))) := by
    intro hu
    rw [← hloc] at hu
    haveI := Localization.isLocalHom_localRingHom (P₁.comap φ) P₁ φ rfl
    apply hπ.not_isUnit
    rw [hπS]
    exact isUnit_of_map_unit (Localization.localRingHom (P₁.comap φ) P₁ φ rfl) _ hu
  have hSS₁ : Function.Injective
      (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    by_contra hx0'
    obtain ⟨n, hn⟩ := IsDiscreteValuationRing.associated_pow_irreducible hx0' hπ
    have h2 := hn.map (algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁))
    rw [hx, map_pow, hπS, hloc] at h2
    exact pow_ne_zero n hx0 (h2.eq_zero_iff.1 rfl)
  have hqS : IsUnit ((q : Localization.AtPrime (P₁.comap φ))) := by
    have := hqA.map (algebraMap A (Localization.AtPrime (P₁.comap φ)))
    rwa [map_natCast] at this
  have hy' : (algebraMap R₁ (Localization.AtPrime P₁) y) ^ q =
      algebraMap (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁)
        (algebraMap A (Localization.AtPrime (P₁.comap φ)) π) := by
    rw [← map_pow, hy, hπS, hloc]
  have hxB : IsUnit (algebraMap R₁ (GlobalTheory.LocAcyc.GenFib A₁ R₁) (φ (algebraMap A R π))) := by
    rw [hφw]
    exact IsLocalization.map_units (GlobalTheory.LocAcyc.GenFib A₁ R₁)
      (⟨algebraMap A₁ R₁ (f π), f π, mem_nonZeroDivisors_of_ne_zero hπ0, rfl⟩ :
        Algebra.algebraMapSubmonoid R₁ (nonZeroDivisors A₁))
  exact etale_closure_core H A R hAR A₁ R₁ hAR₁ φ β hβ DA q act hq htor
    (Localization.AtPrime (P₁.comap φ)) (Localization.AtPrime P₁) hRS hR₁S₁ hloc hSS₁ hqS
    (algebraMap A _ π) hπ (algebraMap R₁ _ y) hy' (φ (algebraMap A R π)) hx0 hxu hxB

end GlobalTheory.KeyOriginTransport
