import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie

namespace GlobalTheory.RepresentativesImage

theorem isReps_image {V W : Type} [AddCommGroup V] [AddCommGroup W] [DecidableEq W] (T : V ≃+ W)
    {Λ₁ Λ₂ : AddSubgroup V} {M₁ M₂ : AddSubgroup W} {S : Finset V}
    (hS : Formalism.L2.Th1.H.IsReps Λ₁ Λ₂ S) (h₁ : ∀ x : V, T x ∈ M₁ ↔ x ∈ Λ₁) (h₂ : ∀ x : V, T x ∈ M₂ ↔ x ∈ Λ₂) :
    Formalism.L2.Th1.H.IsReps M₁ M₂ (Finset.image (⇑T : V → W) S) := by
  unfold Formalism.L2.Th1.H.IsReps at hS ⊢
  obtain ⟨hmem, hdist, hcov⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    exact (h₂ v).2 (hmem v hv)
  · intro a ha b hb hab
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 ha
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hb
    rw [← map_sub] at hab
    rw [hdist v hv u hu ((h₁ _).1 hab)]
  · intro w hw
    obtain ⟨v, rfl⟩ := T.surjective w
    obtain ⟨u, hu, hvu⟩ := hcov v ((h₂ v).1 hw)
    exact ⟨T u, Finset.mem_image_of_mem _ hu, by rw [← map_sub]; exact (h₁ _).2 hvu⟩

end GlobalTheory.RepresentativesImage
