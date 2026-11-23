import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleFaithfullyFlatRingHomBasicProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleCoverModelOfIsColimit
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem etFF_descends_of_isColimit :
    ∀ (J : Type) [SmallCategory J] [IsFiltered J] (D : J ⥤ CommRingCat.{0}) (c : Cocone D),
      IsColimit c → ∀ (B : CommRingCat.{0}) (g : c.pt ⟶ B), EtFF g →
      ∃ (j : J) (B' : CommRingCat.{0}) (g' : D.obj j ⟶ B') (h : B' ⟶ B),
        EtFF g' ∧ IsPushout g' (c.ι.app j) h g := by
  intro J _ _ D c hc B g hg
  obtain ⟨-, hsurj⟩ := (etFF_iff_spec g).1 hg
  obtain ⟨j₀⟩ := IsFiltered.nonempty (C := J)
  obtain ⟨j, -, B', g', h, hgh, hcov⟩ :=
    GlobalTheory.EtaleCoverDescent.exists_etale_cover_model_of_isColimit J D c hc Unit (fun _ ↦ B)
      (fun _ ↦ g) (fun _ ↦ hg.1)
      (fun p ↦ by
        obtain ⟨v, hv⟩ := hsurj.surj p
        exact ⟨(), v, hv⟩) j₀
  refine ⟨j, B' (), g' (), h (), ?_, (hgh ()).2⟩
  rw [etFF_iff_spec]
  refine ⟨HasRingHomProperty.Spec_iff.2 (hgh ()).1, ⟨fun p ↦ ?_⟩⟩
  obtain ⟨i, v, hv⟩ := hcov p
  cases i
  exact ⟨v, hv⟩

end GlobalTheory.EtC
