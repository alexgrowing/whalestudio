import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC

theorem isIndEtale_comp_etale {A B O : Type} [CommRing A] [CommRing B] [CommRing O] (φ : A →+* B)
    (hφ : φ.Etale) (g : B →+* O) (hg : GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale g) :
    GlobalTheory.IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsIndEtale (g.comp φ) := by
  obtain ⟨J, _, _, D, s, t, hs, hj⟩ := hg
  refine ⟨J, inferInstance, inferInstance, D, (Functor.const J).map (CommRingCat.ofHom φ) ≫ s, t, hs,
    fun j => ⟨?_, ?_⟩⟩
  · show RingHom.Etale ((s.app j).hom.comp φ)
    exact RingHom.Etale.stableUnderComposition _ _ hφ (hj j).1
  · have h2 := (hj j).2
    show CommRingCat.ofHom φ ≫ s.app j ≫ t.app j = CommRingCat.ofHom (g.comp φ)
    rw [h2]
    rfl

theorem isStalk_affine : ∀ (A : Type) [CommRing A] (O : Type) [CommRing O]
    (s : Spec (CommRingCat.of O) ⟶ Spec (CommRingCat.of A)), IsStalk O s →
    ∃ _ : Algebra A O, SH O ∧ IndEt A O ∧ s = Spec.map (CommRingCat.ofHom (algebraMap A O)) := by
  intro A _ O _ s hs
  obtain ⟨hSH, A', _, _, j, hj, hind, rfl⟩ := hs
  set φ := Spec.preimage j with hφdef
  have hjφ : Spec.map φ = j := Spec.map_preimage j
  have hφ : φ.hom.Etale := by
    rw [← hjφ] at hj
    exact (HasRingHomProperty.Spec_iff (P := @Etale)).mp hj
  letI : Algebra A O := ((algebraMap A' O).comp φ.hom).toAlgebra
  refine ⟨this, hSH, ?_, ?_⟩
  · exact isIndEtale_comp_etale φ.hom hφ (algebraMap A' O) hind
  · rw [← hjφ, ← Spec.map_comp]
    rfl

end GlobalTheory.EtC
