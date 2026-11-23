import Mathlib
import Formalism.HermitianLattices.DualOrthSum
import Formalism.HermitianLattices.HermitianLatticesProofs.DualBasic

noncomputable section

namespace Formalism.HermitianLatticesTheory

private theorem mem_dual_iff_hermitian_lattices {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem dualOrthSum : DualOrthSum := by
  intro R K V _ _ _ _ _ _ _ _ h V₁ V₂ hc h12 h21 L₁ L₂ hL₁ hL₂
  apply le_antisymm
  · intro x hx
    rw [mem_dual_iff_hermitian_lattices] at hx
    have htop : x ∈ V₁ ⊔ V₂ := by
      rw [hc.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp htop
    refine Submodule.mem_sup.mpr ⟨x₁, Submodule.mem_inf.mpr ⟨?_, hx₁⟩,
      x₂, Submodule.mem_inf.mpr ⟨?_, hx₂⟩, rfl⟩
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₂ = 0 := h12 y (hL₁ hy) x₂ hx₂
      have hm := hx y (Submodule.mem_sup_left hy)
      rwa [map_add, e, add_zero] at hm
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₁ = 0 := h21 y (hL₂ hy) x₁ hx₁
      have hm := hx y (Submodule.mem_sup_right hy)
      rwa [map_add, e, zero_add] at hm
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, LinearMap.add_apply, h21 y₂ (hL₂ hy₂) x hxV, add_zero]
      exact hxd y₁ hy₁
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add, LinearMap.add_apply, h12 y₁ (hL₁ hy₁) x hxV, zero_add]
      exact hxd y₂ hy₂

end Formalism.HermitianLatticesTheory
