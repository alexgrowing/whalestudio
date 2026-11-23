import Development.EtaleCohomology.EtaleSheaves.EtaleDegreeZeroCohomologyEquivLocallyConstantFun
import Mathlib.RingTheory.Spectrum.Prime.RingHom

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.CechLevelsPf
open PrimeSpectrum

theorem qm_comp {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).comp (Ideal.Quotient.mk I) =
      (Ideal.Quotient.mk (I.map φ)).comp φ := Ideal.quotientMap_comp_mk _

theorem qm_integral {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral) :
    (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map).IsIntegral := by
  apply RingHom.IsIntegral.tower_top (Ideal.Quotient.mk I)
  rw [qm_comp]
  exact RingHom.IsIntegral.trans _ _ h (RingHom.isIntegral_of_surjective _ Ideal.Quotient.mk_surjective)

theorem qm_surj {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    Function.Surjective (PrimeSpectrum.comap (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map)) := by
  intro P
  obtain ⟨Q, hQ⟩ := hs (PrimeSpectrum.comap (Ideal.Quotient.mk I) P)
  have hmem : Q ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I.map φ))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker]
    show I.map φ ≤ Q.asIdeal
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    have : x ∈ (PrimeSpectrum.comap φ Q).asIdeal := by
      rw [hQ]; show Ideal.Quotient.mk I x ∈ P.asIdeal; rw [Ideal.Quotient.eq_zero_iff_mem.2 hx]; exact zero_mem _
    exact this
  obtain ⟨Q', rfl⟩ := hmem
  refine ⟨Q', comap_injective_of_surjective _ Ideal.Quotient.mk_surjective ?_⟩
  rw [← hQ, ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply, qm_comp]

theorem spec_surj {A B : Type} [CommRing A] [CommRing B] (f : A →+* B)
    (hs : Function.Surjective (PrimeSpectrum.comap f)) : Surjective (Spec.map (CommRingCat.ofHom f)) := by
  rw [surjective_iff]; exact hs

theorem part1 {A A' : Type} [CommRing A] [CommRing A'] (φ : A →+* A') (I : Ideal A) (h : φ.IsIntegral)
    (hs : Function.Surjective (PrimeSpectrum.comap φ)) :
    IsIntegralHom (Spec.map (CommRingCat.ofHom φ)) ∧ Surjective (Spec.map (CommRingCat.ofHom φ)) ∧
    IsIntegralHom (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) ∧
    Surjective (Spec.map (CommRingCat.ofHom (Ideal.quotientMap (I.map φ) φ Ideal.le_comap_map))) :=
  ⟨IsIntegralHom.SpecMap_iff.2 h, spec_surj _ hs, IsIntegralHom.SpecMap_iff.2 (qm_integral φ I h),
    spec_surj _ (qm_surj φ I hs)⟩

end LateralTheory.E.CechLevelsPf
