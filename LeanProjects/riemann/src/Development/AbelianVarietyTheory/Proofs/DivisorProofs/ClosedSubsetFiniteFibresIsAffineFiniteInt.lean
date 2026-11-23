import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp

theorem ringChar_residueField_eq {X Y : Scheme.{0}} (f : X ⟶ Y) (x : X) :
    ringChar (X.residueField x) = ringChar (Y.residueField (f x)) := by
  haveI := (RingHom.charP_iff_charP (f.residueFieldMap x).hom (ringChar (Y.residueField (f x)))).1
    (ringChar.charP _)
  exact ringChar.eq _ _

theorem closeds_finite_int : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (T : Closeds X), (∀ ℓ : ℕ, ((T : Set X) ∩ fib X ℓ).Finite) →
    IsAffine (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      Module.Finite ℤ Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) := by
  intro k _ X _ p D hX T hT
  set I := Scheme.IdealSheafData.vanishingIdeal T with hI
  have hr : Set.range I.subschemeι = (T : Set X) := by
    rw [Scheme.IdealSheafData.range_subschemeι, hI, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  obtain ⟨N, j, _, hj⟩ := hX.isProjOver
  have := isProper_str k N
  have : IsProper p := hj ▸ inferInstance
  have : IsFinite (spMap (Int.castRingHom k)) :=
    (IsFinite.SpecMap_iff _).2 (RingHom.finite_algebraMap.2 hX.finite)
  set q := I.subschemeι ≫ p ≫ spMap (Int.castRingHom k) with hq
  have : IsProper q := by rw [hq]; infer_instance
  have : LocallyQuasiFinite q := by
    refine LocallyQuasiFinite.of_finite_preimage_singleton _ fun y => ?_
    have hfin := hT (ringChar ((Sp ℤ).residueField y))
    refine Set.Finite.of_finite_image (f := I.subschemeι) (hfin.subset ?_)
      (I.subschemeι.isClosedEmbedding.injective.injOn)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨hr.le ⟨z, rfl⟩, ?_⟩
    show ringChar _ = _
    rw [ringChar_residueField_eq (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z)]
    have e : (p ≫ spMap (Int.castRingHom k)) (I.subschemeι z) = y := by
      rw [← hz, hq]; rfl
    rw [e]
  have : IsFinite q := IsFinite.of_isProper_of_locallyQuasiFinite q
  have hA : IsAffine I.subscheme := isAffine_of_isAffineHom q
  refine ⟨hA, ?_⟩
  have hf : (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom).Finite :=
    q.finite_appTop.comp (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv).2)
  rw [RingHom.ext_int (q.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of ℤ)).inv.hom)
    (algebraMap ℤ Γ(I.subscheme, ⊤)), RingHom.finite_algebraMap] at hf
  exact hf

end GlobalTheory.HSAmp
