import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComapBcComp
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
universe u

namespace GlobalTheory.HilbAff

theorem idealSheafData_ext_of_openCover {X : Scheme.{0}} {ι : Type u} (V : ι → Scheme.{0})
    (f : ∀ i, V i ⟶ X) (hf : ∀ i, IsOpenImmersion (f i)) (hcov : ∀ x : X, ∃ i y, f i y = x)
    (I I' : X.IdealSheafData) (h : ∀ i, I.comap (f i) = I'.comap (f i)) : I = I' := by
  refine Scheme.IdealSheafData.ext_of_iSup_eq_top
    (ι := Σ i, (V i).affineOpens)
    (fun p => ⟨(f p.1) ''ᵁ p.2.1, p.2.2.image_of_isOpenImmersion (f p.1)⟩) ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, rfl⟩ := hcov x
    have hy : y ∈ (⊤ : (V i).Opens) := trivial
    rw [← iSup_affineOpens_eq_top (V i)] at hy
    obtain ⟨W, hW⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨i, W⟩, ⟨y, hW, rfl⟩⟩
  · rintro ⟨i, W⟩
    have e := congrArg (fun J => J.ideal W) (h i)
    simp only [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion] at e
    exact Ideal.comap_injective_of_surjective _
      ((ConcreteCategory.bijective_of_isIso ((f i).appIso W).inv).2) e

end GlobalTheory.HilbAff
