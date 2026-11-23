import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_eq_toMorphismProperty :
    EtFF = RingHom.toMorphismProperty (fun f => RingHom.Etale f ∧ RingHom.FaithfullyFlat f) := by
  ext A B g; rfl

theorem etFF_iff_spec {A B : CommRingCat.{0}} (g : A ⟶ B) :
    EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g) := by
  have he : Etale (Spec.map g) ↔ g.hom.Etale := HasRingHomProperty.Spec_iff
  have hs : Surjective (Spec.map g) ↔ Function.Surjective (PrimeSpectrum.comap g.hom) := by
    rw [surjective_iff]; rfl
  rw [he, hs]
  change g.hom.Etale ∧ g.hom.FaithfullyFlat ↔ _
  rw [RingHom.FaithfullyFlat.iff_flat_and_comap_surjective]
  constructor
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, (RingHom.Etale.iff_flat_and_formallyUnramified.1 h1).1, h2⟩

theorem etFF_isMultiplicative : EtFF.IsMultiplicative where
  id_mem A := ⟨RingHom.Etale.of_bijective Function.bijective_id,
    RingHom.FaithfullyFlat.of_bijective Function.bijective_id⟩
  comp_mem f g hf hg := by
    change (f ≫ g).hom.Etale ∧ (f ≫ g).hom.FaithfullyFlat
    rw [CommRingCat.hom_comp]
    exact ⟨RingHom.Etale.stableUnderComposition _ _ hf.1 hg.1,
      RingHom.FaithfullyFlat.stableUnderComposition _ _ hf.2 hg.2⟩

theorem etFF_isStableUnderCobaseChange : EtFF.IsStableUnderCobaseChange := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.isStableUnderCobaseChange_toMorphismProperty_iff.2
    (RingHom.Etale.isStableUnderBaseChange.and RingHom.FaithfullyFlat.isStableUnderBaseChange)

theorem etFF_respectsIso : EtFF.RespectsIso := by
  rw [etFF_eq_toMorphismProperty]
  exact RingHom.toMorphismProperty_respectsIso_iff.1
    (RingHom.Etale.respectsIso.and RingHom.FaithfullyFlat.respectsIso)

theorem finiteType_of_etFF {A B : CommRingCat.{0}} (g : A ⟶ B) (hg : EtFF g)
    (hA : Algebra.FiniteType ℤ A) : Algebra.FiniteType ℤ B := by
  letI := g.hom.toAlgebra
  haveI : Algebra.Etale A B := RingHom.Etale.toAlgebra hg.1
  exact Algebra.FiniteType.trans hA inferInstance

theorem etFF_basic :
    (EtFF.IsMultiplicative ∧ EtFF.IsStableUnderCobaseChange ∧ EtFF.RespectsIso) ∧
    (∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g ↔ Etale (Spec.map g) ∧ Surjective (Spec.map g)) ∧
    ∀ (A B : CommRingCat.{0}) (g : A ⟶ B), EtFF g → Algebra.FiniteType ℤ A → Algebra.FiniteType ℤ B :=
  ⟨⟨etFF_isMultiplicative, etFF_isStableUnderCobaseChange, etFF_respectsIso⟩,
    fun _ _ g => etFF_iff_spec g, fun _ _ g hg hA => finiteType_of_etFF g hg hA⟩

end GlobalTheory.EtC
