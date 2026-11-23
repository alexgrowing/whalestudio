import Mathlib

noncomputable section

namespace GlobalTheory.AffineCurveNbhd

def IsNbhd (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] (f : A) : Prop :=
  (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) ∧
  (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f})

theorem awayHom_isUnit {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) :
    IsUnit (((algebraMap A'' (Localization.Away (algebraMap A A'' f))).comp φ.toRingHom) (algebraMap A A' f)) := by
  rw [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, AlgHom.commutes]
  exact IsLocalization.Away.algebraMap_isUnit _

def awayHom {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A'] [Algebra A A'']
    (φ : A' →ₐ[A] A'') (f : A) : Localization.Away (algebraMap A A' f) →+* Localization.Away (algebraMap A A'' f) :=
  Localization.awayLift ((algebraMap A'' _).comp φ.toRingHom) _ (awayHom_isUnit φ f)

theorem awayHom_comp_algebraMap {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra A A']
    [Algebra A A''] (φ : A' →ₐ[A] A'') (f : A) :
    (awayHom φ f).comp (algebraMap A' _) = (algebraMap A'' _).comp φ.toRingHom :=
  IsLocalization.Away.lift_comp _ (awayHom_isUnit φ f)

end GlobalTheory.AffineCurveNbhd

end
