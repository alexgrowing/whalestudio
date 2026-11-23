import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsExcisionNbhdSelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalizationPullbackInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayCongrModOfIsCoprimeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AwayMapSpanSingletonDivisibilityDescendsStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.MVGlue

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Functor.map_comp]

theorem etale_awayMap : ∀ (A C : Type) [CommRing A] [CommRing C] [Algebra A C] [Algebra.Etale A C] (f : A), @Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) _ _ (Localization.awayMap (algebraMap A C) f).toAlgebra := by
  intro A C _ _ _ _ f
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale C (Localization.Away (algebraMap A C f)) := Algebra.Etale.of_isLocalizationAway (algebraMap A C f)
  haveI : Algebra.Etale A (Localization.Away f) := Algebra.Etale.of_isLocalizationAway f
  haveI : Algebra.Etale A (Localization.Away (algebraMap A C f)) := Algebra.Etale.comp A C _
  haveI : IsScalarTower A (Localization.Away f) (Localization.Away (algebraMap A C f)) := by
    refine IsScalarTower.of_algebraMap_eq (fun a => ?_)
    show _ = Localization.awayMap (algebraMap A C) f (algebraMap A (Localization.Away f) a)
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsScalarTower.algebraMap_apply A C (Localization.Away (algebraMap A C f))]
  exact Algebra.Etale.of_restrictScalars A _ _

theorem pull_spMap_comp (q : ℕ) {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C)
    (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (g.comp f)) _ _ x = pull _ (spMap g) _ _ (pull _ (spMap f) _ _ x) := by
  rw [spMap_comp', pull_comp]

theorem pull_spMap_id (q : ℕ) {A : Type} [CommRing A] (n i : ℤ) (x : Ht q (sp A) n i) :
    pull _ (spMap (RingHom.id A)) _ _ x = x := by
  have : spMap (RingHom.id A) = 𝟙 (sp A) := by
    simp only [spMap, CommRingCat.ofHom_id, Spec.map_id]
    exact sch.map_id _
  rw [this, pull_id]

theorem glue : ∀ (q : ℕ) (A C : Type) [CommRing A] [CommRing C] [Algebra A C] (f g : A), IsCoprime f g → IsExcisionNbhd A C g → ∀ (n i : ℤ) (a : Ht q (sp (Localization.Away (f * g))) n i), pull _ (spMap (Localization.awayMap (algebraMap A C) (f * g))) _ _ a = 0 → ∃ b : Ht q (sp (Localization.Away f)) n i, ∀ ρ : Localization.Away f →+* Localization.Away (f * g), ρ.comp (algebraMap A _) = algebraMap A _ → pull _ (spMap ρ) _ _ b = a := by
  intro q A C _ _ _ f g hfg hC n i a ha
  obtain ⟨hEt, h1, h2⟩ := hC
  letI : Algebra (Localization.Away f) (Localization.Away (algebraMap A C f)) :=
    (Localization.awayMap (algebraMap A C) f).toAlgebra
  haveI : Algebra.Etale (Localization.Away f) (Localization.Away (algebraMap A C f)) := etale_awayMap A C f
  have hB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) =
      Localization.awayMap (algebraMap A C) f := rfl
  set h : Localization.Away f := algebraMap A (Localization.Away f) g with hh
  have c1 := GlobalTheory.T.away_congr_mod_of_isCoprime A C f g hfg h1
  have c2 := GlobalTheory.T.awayMap_span_singleton_divisibility_descends A C f g h2
  rw [← hB] at c1 c2

  have hu1 : IsUnit (((algebraMap (Localization.Away f) (Localization.Away h)).comp
      (algebraMap A (Localization.Away f))) (f * g)) := by
    rw [map_mul, RingHom.comp_apply, RingHom.comp_apply]
    refine IsUnit.mul ?_ ?_
    · exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away f) f).map
        (algebraMap (Localization.Away f) (Localization.Away h))
    · exact IsLocalization.Away.algebraMap_isUnit (S := Localization.Away h) h
  let ψ : Localization.Away (f * g) →+* Localization.Away h :=
    IsLocalization.Away.lift (S := Localization.Away (f * g)) (f * g) hu1
  have hψ : ∀ x : A, ψ (algebraMap A _ x) = algebraMap _ _ (algebraMap A (Localization.Away f) x) := fun x => by
    simp only [ψ, IsLocalization.Away.lift_eq, RingHom.comp_apply]
  have hgB : algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h =
      algebraMap C (Localization.Away (algebraMap A C f)) (algebraMap A C g) := by
    rw [hB, hh]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
  have hu2 : IsUnit (((algebraMap (Localization.Away (algebraMap A C f))
      (Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h))).comp
      (algebraMap C (Localization.Away (algebraMap A C f)))) (algebraMap A C (f * g))) := by
    rw [map_mul, map_mul, RingHom.comp_apply, RingHom.comp_apply, ← hgB]
    refine IsUnit.mul ?_ (IsLocalization.Away.algebraMap_isUnit _)
    exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away (algebraMap A C f)) (algebraMap A C f)).map _
  let χ : Localization.Away (algebraMap A C (f * g)) →+*
      Localization.Away (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f)) h) :=
    IsLocalization.Away.lift (S := Localization.Away (algebraMap A C (f * g))) (algebraMap A C (f * g)) hu2
  have hsq : (Localization.awayMap (algebraMap (Localization.Away f) (Localization.Away (algebraMap A C f))) h).comp ψ =
      χ.comp (Localization.awayMap (algebraMap A C) (f * g)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, χ]
    simp [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq, IsLocalization.Away.lift_eq, hB]
  obtain ⟨b, hb, -⟩ := GlobalTheory.T.localization_pullback_injective q (Localization.Away f) (Localization.Away (algebraMap A C f)) h c1 c2 n i
    (pull _ (spMap ψ) _ _ a) 0 (by
      rw [map_zero, ← pull_spMap_comp, hsq, pull_spMap_comp, ha, map_zero])
  refine ⟨b, fun ρ hρ => ?_⟩
  have hρu : IsUnit (ρ h) := by
    rw [hh, ← RingHom.comp_apply, hρ, map_mul] at *
    exact isUnit_of_mul_isUnit_right (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (f * g))
  let ψ' : Localization.Away h →+* Localization.Away (f * g) :=
    IsLocalization.Away.lift (S := Localization.Away h) h hρu
  have h1' : ψ'.comp (algebraMap (Localization.Away f) (Localization.Away h)) = ρ :=
    IsLocalization.Away.lift_comp _ _
  have h2' : ψ'.comp ψ = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (f * g))
    ext x
    simp only [RingHom.comp_apply, hψ, ψ', IsLocalization.Away.lift_eq, RingHom.id_apply]
    rw [← RingHom.comp_apply ρ, hρ]
  rw [← h1', pull_spMap_comp, hb, ← pull_spMap_comp, h2', pull_spMap_id]

end GlobalTheory.MVGlue
