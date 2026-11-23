import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsorsTrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OriginIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureFiniteEtale
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
open IsLocalRing Polynomial
open scoped TensorProduct

namespace GlobalTheory.KeyOriginNoeth

theorem isIntegrallyClosedIn_closure_localization : ∀ (A R : Type) [CommRing A] [IsDomain A] [CommRing R] [IsDomain R] [IsNoetherianRing R]
    [IsIntegrallyClosed R] [Algebra A R], Function.Injective (algebraMap A R) →
    ∀ (D : Type) [CommRing D] [Algebra (GlobalTheory.LocAcyc.GenFib A R) D]
    [Module.Finite (GlobalTheory.LocAcyc.GenFib A R) D] [Algebra.Etale (GlobalTheory.LocAcyc.GenFib A R) D],
    letI := GlobalTheory.KeyOriginNoeth.closureAlg A R D
    IsIntegrallyClosedIn (GlobalTheory.KeyOriginNoeth.closure A R D)
      (Localization (Algebra.algebraMapSubmonoid (GlobalTheory.KeyOriginNoeth.closure A R D)
        (nonZeroDivisors R))) := by
  intro A R _ _ _ _ _ _ _ hinj D _ _ _ _
  letI := closureAlg A R D
  let M : Submonoid R := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  have hM : M ≤ nonZeroDivisors R := by
    rintro _ ⟨a, ha, rfl⟩
    refine mem_nonZeroDivisors_of_ne_zero fun h => nonZeroDivisors.ne_zero ha ?_
    exact hinj (h.trans (map_zero _).symm)
  haveI : IsDomain (GlobalTheory.LocAcyc.GenFib A R) := IsLocalization.isDomain_of_le_nonZeroDivisors _ hM
  haveI : IsIntegrallyClosed (GlobalTheory.LocAcyc.GenFib A R) :=
    isIntegrallyClosed_of_isLocalization (GlobalTheory.LocAcyc.GenFib A R) M hM
  have hRGF : Function.Injective (algebraMap R (GlobalTheory.LocAcyc.GenFib A R)) :=
    IsLocalization.injective (GlobalTheory.LocAcyc.GenFib A R) hM
  have h1 : IsIntegrallyClosedIn D (D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R)) :=
    GlobalTheory.isIntegrallyClosedIn_tensor_of_smooth
  obtain ⟨hDinj, hDcl⟩ := isIntegrallyClosedIn_iff.mp h1
  let g : closure A R D →+* D ⊗[GlobalTheory.LocAcyc.GenFib A R] FractionRing (GlobalTheory.LocAcyc.GenFib A R) :=
    (algebraMap D _).comp (closure A R D).subtype
  have hg : Function.Injective g := hDinj.comp Subtype.val_injective
  have hunit : ∀ n : Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R), IsUnit (g n) := by
    rintro ⟨_, s, hs, rfl⟩
    have hs0 : algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s ≠ 0 := by
      intro h
      exact nonZeroDivisors.ne_zero hs (hRGF (h.trans (map_zero _).symm))
    have hL : IsUnit (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
        (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) :=
      ((IsFractionRing.injective (GlobalTheory.LocAcyc.GenFib A R) _).ne_iff' (map_zero _)).mpr hs0 |>.isUnit
    have heq : g (algebraMap R (closure A R D) s) = Algebra.TensorProduct.includeRight
        (algebraMap (GlobalTheory.LocAcyc.GenFib A R) (FractionRing (GlobalTheory.LocAcyc.GenFib A R))
          (algebraMap R (GlobalTheory.LocAcyc.GenFib A R) s)) := by
      rw [Algebra.TensorProduct.includeRight.commutes]
      rfl
    rw [heq]
    exact hL.map _
  let φ := IsLocalization.lift (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
    (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) hunit
  have hφ : φ.comp (algebraMap (closure A R D) _) = g := IsLocalization.lift_comp _

  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨c, n⟩, rfl⟩ := IsLocalization.mk'_surjective
      (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R)) z
    have hc : g c = 0 := by
      have := (IsLocalization.lift_mk'_spec (M := Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))
        (S := Localization (Algebra.algebraMapSubmonoid (closure A R D) (nonZeroDivisors R))) (hg := hunit) c 0 n).mp hz
      rw [mul_zero] at this
      exact this
    have : c = 0 := hg (hc.trans (map_zero g).symm)
    simp only [this, IsLocalization.mk'_zero]
  refine isIntegrallyClosedIn_iff.mpr ⟨?_, fun {x} hx => ?_⟩
  · intro a b hab
    apply hg
    rw [← hφ, RingHom.comp_apply, RingHom.comp_apply, hab]
  · obtain ⟨p, hp, hpx⟩ := hx
    have hev : Polynomial.eval₂ g (φ x) p = 0 := by
      have := Polynomial.hom_eval₂ p (algebraMap (closure A R D) _) φ x
      rw [hpx, map_zero, hφ] at this
      exact this.symm
    have hxD : IsIntegral D (φ x) := by
      refine ⟨p.map (closure A R D).subtype, hp.map _, ?_⟩
      rw [Polynomial.eval₂_map]
      exact hev
    obtain ⟨d, hd⟩ := hDcl hxD

    have hdC : Polynomial.eval₂ (closure A R D).subtype d p = 0 := by
      apply hDinj
      rw [Polynomial.hom_eval₂, hd, map_zero]
      exact hev
    have hdmem : d ∈ closure A R D := by
      letI : Algebra R D := (baseHom A R D).toAlgebra
      letI : Algebra (closure A R D) D := (closure A R D).subtype.toAlgebra
      haveI : IsScalarTower R (closure A R D) D := .of_algebraMap_eq fun _ => rfl
      haveI : Algebra.IsIntegral R (closure A R D) := ⟨fun c => by
        let f : closure A R D →ₐ[R] D := { (closure A R D).subtype with commutes' := fun _ => rfl }
        exact (isIntegral_algHom_iff f Subtype.val_injective).mp c.2⟩
      have hxC : IsIntegral (closure A R D) d := ⟨p, hp, hdC⟩
      exact isIntegral_trans _ hxC
    refine ⟨⟨d, hdmem⟩, hφinj ?_⟩
    rw [← RingHom.comp_apply, hφ]
    exact hd

end GlobalTheory.KeyOriginNoeth
