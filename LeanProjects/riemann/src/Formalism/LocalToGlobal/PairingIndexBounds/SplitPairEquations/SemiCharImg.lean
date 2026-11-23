import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.QuadraticSemicharacterIdentityReformulated2

noncomputable section
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq

open Formalism.L2.Th1.H

section
variable {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (δ : V ≃ₗ[ℂ] V)

theorem semiChar_img (hI : IsIsom H H (δ : V →ₗ[ℂ] V)) (hα : ∀ x, α (δ x) = α x) {Λ : AddSubgroup V}
    (h : IsSemiChar H Λ α) : IsSemiChar H (imgLat (δ : V →ₗ[ℂ] V) Λ) α := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    show α (δ x) = 1 ∨ α (δ x) = -1
    rw [hα]; exact h.1 x hx
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    show α (δ x + δ y) = α (δ x) * α (δ y) * Complex.exp ((Real.pi : ℂ) * Complex.I * (altE H (δ x) (δ y) : ℂ))
    have : altE H (δ x) (δ y) = altE H x y := by simp only [altE]; rw [show H (δ x) (δ y) = H x y from hI x y]
    rw [← map_add, hα, hα, hα, this, h.2 x hx y hy]

theorem fixed_img (hI : IsIsom H H (δ : V →ₗ[ℂ] V)) (hα : ∀ x, α (δ x) = α x) {Λ : AddSubgroup V} {F : V → ℂ}
    (hF : F ∈ fixedBy H α Λ) : pullInv δ F ∈ fixedBy H α (imgLat (δ : V →ₗ[ℂ] V) Λ) := by
  rintro _ ⟨x, hx, rfl⟩ z
  show α (δ x) * opU H (δ x) (pullInv δ F) z = pullInv δ F z
  rw [← pullOpU V H δ hI x F z, hα]
  exact hF x hx (δ.symm z)

theorem reps_img {Λ₁ Λ₂ : AddSubgroup V} {S : Finset V} (hS : IsReps Λ₁ Λ₂ S) :
    IsReps (imgLat (δ : V →ₗ[ℂ] V) Λ₁) (imgLat (δ : V →ₗ[ℂ] V) Λ₂) (S.image δ) := by
  obtain ⟨h1, h2, h3⟩ := hS
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    exact ⟨s, h1 s hs, rfl⟩
  · intro x hx y hy hxy
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨u, hu, hu'⟩ := hxy
    have e : u = s - t := δ.injective (by rw [map_sub]; exact hu')
    rw [h2 s hs t ht (e ▸ hu)]
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨s, hs, hus⟩ := h3 u hu
    refine ⟨δ s, Finset.mem_image.mpr ⟨s, hs, rfl⟩, ⟨u - s, hus, ?_⟩⟩
    show δ (u - s) = δ u - δ s
    rw [map_sub]

theorem relIdx_img (Λ₁ Λ₂ : AddSubgroup V) :
    relIdx (imgLat (δ : V →ₗ[ℂ] V) Λ₁) (imgLat (δ : V →ₗ[ℂ] V) Λ₂) = relIdx Λ₁ Λ₂ :=
  AddSubgroup.relIndex_map_map_of_injective Λ₁ Λ₂ (f := ((δ : V →ₗ[ℂ] V).toAddMonoidHom)) δ.injective

theorem sumU_pull (hI : IsIsom H H (δ : V →ₗ[ℂ] V)) (hα : ∀ x, α (δ x) = α x) (S : Finset V) (F : V → ℂ) (z : V) :
    pullInv δ (sumU H α S F) z = sumU H α (S.image δ) (pullInv δ F) z := by
  unfold sumU
  rw [Finset.sum_image (fun x _ y _ h => δ.injective h)]
  show ∑ x ∈ S, α x * opU H x F (δ.symm z) = _
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hα, ← pullOpU V H δ hI x F z]
  rfl

theorem inter_pull (hH : IsHerm H) (hI : IsIsom H H (δ : V →ₗ[ℂ] V)) (hα : ∀ x, α (δ x) = α x)
    (Λ₁ Λ₂ : AddSubgroup V) (hs : IsSemiChar H Λ₂ α) (hidx : relIdx Λ₁ Λ₂ ≠ 0) {F : V → ℂ}
    (hF : F ∈ fixedBy H α Λ₁) :
    pullInv δ (inter H α Λ₁ Λ₂ F) =
      inter H α (imgLat (δ : V →ₗ[ℂ] V) Λ₁) (imgLat (δ : V →ₗ[ℂ] V) Λ₂) (pullInv δ F) := by
  funext z
  obtain ⟨S, hS⟩ := (repsExist V Λ₁ Λ₂ hidx).1
  rw [interReps V H hH _ _ α (semiChar_img H α δ hI hα hs) _ (fixed_img H α δ hI hα hF) _ (reps_img δ hS) z,
    relIdx_img, ← sumU_pull H α δ hI hα]
  show inter H α Λ₁ Λ₂ F (δ.symm z) = _
  rw [interReps V H hH _ _ α hs _ hF _ hS]
  rfl

end

end Formalism.L2.PairingIndexBounds.Eq
