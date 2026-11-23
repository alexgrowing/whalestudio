import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericFiniteMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenFiniteCompDegreeMul
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits
open GlobalTheory.IndefiniteRowSideFullHecke.GenericFiniteMaps

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GenFiniteFibre

theorem eq_bot_of_isField {R : Type} [CommRing R] (h : IsField R) (P : Ideal R) [hP : P.IsPrime] :
    P = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  by_contra h0
  obtain ⟨b, hb⟩ := h.mul_inv_cancel h0
  exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hb ▸ P.mul_mem_right b ha))

theorem eq_genericPoint_of_isField {X : Scheme.{0}} [IsIntegral X] (x : X)
    (h : IsField (X.presheaf.stalk x)) : x = genericPoint X := by
  have hη : genericPoint X ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact genericPoint_specializes x
  obtain ⟨p, hp⟩ := hη
  have hx : X.fromSpecStalk x (IsLocalRing.closedPoint (X.presheaf.stalk x)) = x :=
    Scheme.fromSpecStalk_closedPoint
  have : p = IsLocalRing.closedPoint (X.presheaf.stalk x) :=
    PrimeSpectrum.ext ((@eq_bot_of_isField _ _ h _ p.2).trans (eq_bot_of_isField h _).symm)
  rw [← hp, this, hx]

theorem eq_genericPoint_of_apply_eq : ∀ (T T' : Scheme.{0}) [IsIntegral T] [IsIntegral T'] (ρ : T' ⟶ T) (d : ℕ), IsGenFinite ρ d → ∀ x : T', ρ x = genericPoint T → x = genericPoint T' := by
  intro T T' _ _ ρ d hρ x hx
  have := hρ.isDominant
  have hη : ρ (genericPoint T') = ρ x :=
    (GlobalTheory.GenFiniteComp.apply_genericPoint ρ).trans hx.symm
  have hsp : genericPoint T' ⤳ x := genericPoint_specializes x
  have hcomm := Scheme.Hom.stalkSpecializes_stalkMap ρ (genericPoint T') x hsp

  have hfin₁ : (ρ.stalkMap (genericPoint T')).hom.Finite := by
    have h := hρ.finrank_eq
    have hA : IsField (T.presheaf.stalk (ρ (genericPoint T'))) :=
      GlobalTheory.GenFiniteComp.isField_stalk_apply ρ
    letI := hA.toField
    letI := (ρ.stalkMap (genericPoint T')).hom.toAlgebra
    exact Module.finite_of_finrank_pos (h ▸ hρ.pos)

  have hbij : Function.Bijective
      (T.presheaf.stalkSpecializes (hsp.map ρ.continuous)).hom :=
    ConcreteCategory.bijective_of_isIso
      (T.presheaf.stalkCongr (Inseparable.of_eq hη.symm)).hom
  have hfin₂ : (T.presheaf.stalkSpecializes (hsp.map ρ.continuous) ≫
      ρ.stalkMap (genericPoint T')).hom.Finite :=
    hfin₁.comp (RingHom.Finite.of_surjective _ hbij.2)
  rw [hcomm] at hfin₂
  have hinj : Function.Injective (T'.presheaf.stalkSpecializes hsp).hom :=
    IsFractionRing.injective (T'.presheaf.stalk x) T'.functionField
  have hint : (ρ.stalkMap x).hom.IsIntegral :=
    RingHom.IsIntegral.tower_bot _ _ hinj hfin₂.to_isIntegral
  have hA : IsField (T.presheaf.stalk (ρ x)) := by
    rw [← hη]; exact GlobalTheory.GenFiniteComp.isField_stalk_apply ρ
  letI := (ρ.stalkMap x).hom.toAlgebra
  haveI : Algebra.IsIntegral (T.presheaf.stalk (ρ x)) (T'.presheaf.stalk x) := ⟨hint⟩
  exact eq_genericPoint_of_isField x (isField_of_isIntegral_of_isField' hA)

end GlobalTheory.GenFiniteFibre
