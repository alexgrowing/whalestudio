import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFilteredColimitEtaleOfIndEtStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyTwistedFilteredColimitContinuityStatement
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem exists_etale_kill_of_indEt : ∀ (q : ℕ) (B O : Type) [CommRing B] [CommRing O] [Algebra B O], IsUnit (q : B) → IndEt B O → ∀ (n i : ℤ) (y : Ht q (sp B) n i), pull _ (spMap (algebraMap B O)) _ _ y = 0 → ∃ (D : Type) (_ : CommRing D) (_ : Algebra B D) (_ : Algebra.Etale B D) (_ : D →ₐ[B] O), pull _ (spMap (algebraMap B D)) _ _ y = 0 := by
  intro q B O _ _ _ hq hO n i y hy
  obtain ⟨J, _, _, D, ι, ⟨hc⟩, het⟩ := GlobalTheory.T.exists_filtered_colimit_of_etale_of_indEt B O hO
  have hc' : IsColimit ((Under.forget (CommRingCat.of B)).mapCocone (Cocone.mk _ ι)) :=
    isColimitOfPreserves (Under.forget _) hc
  obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
  have hqj : IsUnit ((q : ((D ⋙ Under.forget _).obj j))) := by
    have := hq.map (D.obj j).hom.hom
    rw [map_natCast] at this
    exact this
  have hyj : pull _ (spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom) _ _
      (pull _ (spMap (D.obj j).hom.hom) _ _ y) = 0 := by
    erw [← pull_comp]
    have hw : (D.obj j).hom ≫ (ι.app j).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app j)
    have : spMap ((Under.forget _).mapCocone (Cocone.mk _ ι) |>.ι.app j).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B O) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hw
    erw [this]; exact hy
  obtain ⟨k, f, hk⟩ := (GlobalTheory.T.etaleCohomology_twisted_filtered_colimit_continuity q (D ⋙ Under.forget _) _ hc' n i).2 j _ hqj hyj
  erw [← pull_comp] at hk
  have hwk : (D.obj j).hom ≫ (D.map f).right = (D.obj k).hom := by simpa using Under.w (D.map f)
  letI : Algebra B (D.obj k).right := (D.obj k).hom.hom.toAlgebra
  refine ⟨(D.obj k).right, inferInstance, this, het k, ⟨(ι.app k).right.hom, fun b => ?_⟩, ?_⟩
  · have hw : (D.obj k).hom ≫ (ι.app k).right = CommRingCat.ofHom (algebraMap B O) := by
      simpa using Under.w (ι.app k)
    exact congrArg (fun g => g.hom b) hw
  · have : spMap ((D ⋙ Under.forget _).map f).hom ≫ spMap (D.obj j).hom.hom
        = spMap (algebraMap B (D.obj k).right) := by
      simp only [spMap, ← Functor.map_comp, ← Spec.map_comp]
      congr 2 <;> simpa using hwk
    erw [this] at hk; exact hk

end GlobalTheory.EtC
