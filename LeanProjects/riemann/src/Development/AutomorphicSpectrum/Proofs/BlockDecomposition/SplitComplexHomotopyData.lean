import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LiftSemiTmul

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.PerfVB

theorem exists_contraction_onto_homology (R P₀ P₁ P₂ : Type) [CommRing R] [AddCommGroup P₀]
    [AddCommGroup P₁] [AddCommGroup P₂] [Module R P₀] [Module R P₁] [Module R P₂]
    (a₀ : P₀ →ₗ[R] P₁) (a₁ : P₁ →ₗ[R] P₂) (t : P₁ →ₗ[R] P₀) (s : P₂ →ₗ[R] P₁) :
    a₁ ∘ₗ a₀ = 0 → a₀ ∘ₗ t ∘ₗ a₀ = a₀ → a₁ ∘ₗ s ∘ₗ a₁ = a₁ →
    ∃ (j : Hc a₀ a₁ →ₗ[R] P₁) (π : P₁ →ₗ[R] Hc a₀ a₁) (h : P₁ →ₗ[R] P₀) (h' : P₂ →ₗ[R] P₁),
      π ∘ₗ j = LinearMap.id ∧ a₁ ∘ₗ j = 0 ∧ π ∘ₗ a₀ = 0 ∧
        j ∘ₗ π + a₀ ∘ₗ h + h' ∘ₗ a₁ = LinearMap.id := by
  intro h10 ht hs
  have h10' : ∀ y, a₁ (a₀ y) = 0 := fun y => LinearMap.congr_fun h10 y
  have ht' : ∀ y, a₀ (t (a₀ y)) = a₀ y := fun y => LinearMap.congr_fun ht y
  have hs' : ∀ x, a₁ (s (a₁ x)) = a₁ x := fun x => LinearMap.congr_fun hs x
  have hk : ∀ x, x - s (a₁ x) ∈ LinearMap.ker a₁ := fun x => by
    rw [LinearMap.mem_ker, map_sub, hs', sub_self]
  have hp : Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) ≤
      LinearMap.ker ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) := by
    rintro ⟨z, hz⟩ hzN
    obtain ⟨y, rfl⟩ : ∃ y, a₀ y = z := LinearMap.mem_range.1 (Submodule.mem_comap.1 hzN)
    rw [LinearMap.mem_ker]
    change a₀ y - a₀ (t (a₀ y)) = 0
    rw [ht', sub_self]
  refine ⟨Submodule.liftQ _ ((LinearMap.id - a₀ ∘ₗ t) ∘ₗ (LinearMap.ker a₁).subtype) hp,
    (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)).mkQ ∘ₗ
      LinearMap.codRestrict (LinearMap.ker a₁) (LinearMap.id - s ∘ₗ a₁) hk,
    t - t ∘ₗ s ∘ₗ a₁, s, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    have key : (⟨z - a₀ (t z) - s (a₁ (z - a₀ (t z))), hk _⟩ : LinearMap.ker a₁) - ⟨z, hz⟩ ∈
        Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀) := by
      refine Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨-t z, ?_⟩)
      change a₀ (-t z) = z - a₀ (t z) - s (a₁ (z - a₀ (t z))) - z
      rw [map_sub a₁, hz', h10', sub_self, map_zero, sub_zero, map_neg]
      abel
    exact (Submodule.Quotient.eq _).2 key
  · refine LinearMap.ext fun q => ?_
    obtain ⟨⟨z, hz⟩, rfl⟩ := Submodule.Quotient.mk_surjective
      (Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀)) q
    have hz' : a₁ z = 0 := LinearMap.mem_ker.1 hz
    change a₁ (z - a₀ (t z)) = 0
    rw [map_sub, hz', h10', sub_zero]
  · refine LinearMap.ext fun y => ?_
    change Submodule.Quotient.mk (p := Submodule.comap (LinearMap.ker a₁).subtype (LinearMap.range a₀))
      (⟨a₀ y - s (a₁ (a₀ y)), hk _⟩ : LinearMap.ker a₁) = 0
    refine (Submodule.Quotient.mk_eq_zero _).2 (Submodule.mem_comap.2 (LinearMap.mem_range.2 ⟨y, ?_⟩))
    change a₀ y = a₀ y - s (a₁ (a₀ y))
    rw [h10', map_zero, sub_zero]
  · refine LinearMap.ext fun x => ?_
    change x - s (a₁ x) - a₀ (t (x - s (a₁ x))) + a₀ (t x - t (s (a₁ x))) + s (a₁ x) = x
    simp only [map_sub]
    abel

end GlobalTheory.CompanionTheory.PerfVB
