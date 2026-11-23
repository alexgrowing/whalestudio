import Mathlib

namespace GlobalTheory

open Module

theorem pairing_surjective_of_separating {M N : Type} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [FiniteDimensional ℂ N] (b : M →ₗ[ℂ] N →ₗ[ℂ] ℂ)
    (hb : ∀ u, u ≠ 0 → ∃ v, b v u ≠ 0) : Function.Surjective b := by
  rw [← LinearMap.range_eq_top]
  have hco : (LinearMap.range b).dualCoannihilator = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    rw [Submodule.mem_dualCoannihilator] at hu
    by_contra h0
    obtain ⟨v, hv⟩ := hb u h0
    exact hv (hu _ ⟨v, rfl⟩)
  rw [← Subspace.dualCoannihilator_dualAnnihilator_eq (W := LinearMap.range b), hco,
    Submodule.dualAnnihilator_bot]

theorem tensor_pairing_separating : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (M N : ι → Type)
    [∀ τ, AddCommGroup (M τ)] [∀ τ, Module ℂ (M τ)] [∀ τ, AddCommGroup (N τ)]
    [∀ τ, Module ℂ (N τ)] [∀ τ, FiniteDimensional ℂ (N τ)] (b : ∀ τ, M τ →ₗ[ℂ] N τ →ₗ[ℂ] ℂ),
    (∀ τ u, u ≠ 0 → ∃ v, b τ v u ≠ 0) →
    ∃ B : MultilinearMap ℂ M (Module.Dual ℂ (PiTensorProduct ℂ N)),
      (∀ v x, B v (PiTensorProduct.tprod ℂ x) = ∏ τ, b τ (v τ) (x τ)) ∧
      ∀ u, u ≠ 0 → ∃ v, B v u ≠ 0 := by
  intro ι _ _ M N _ _ _ _ _ b hb
  refine ⟨(PiTensorProduct.dualDistrib (R := ℂ) (M := N)).compMultilinearMap
    ((PiTensorProduct.tprod ℂ).compLinearMap b), ?_, ?_⟩
  · intro v x
    simp [PiTensorProduct.dualDistrib_apply]
  · intro u hu
    let e : ∀ τ, Basis (Fin (finrank ℂ (N τ))) ℂ (N τ) := fun τ => Module.finBasis ℂ (N τ)
    let E := Basis.piTensorProduct e
    obtain ⟨k, hk⟩ : ∃ k, E.repr u k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hu (E.repr.injective (by ext k; simp [h k]))
    have hs : ∀ τ, ∃ v, b τ v = (e τ).coord (k τ) := fun τ =>
      pairing_surjective_of_separating (b τ) (hb τ) _
    choose v hv using hs
    refine ⟨v, ?_⟩
    have key : (PiTensorProduct.dualDistrib (R := ℂ) (M := N))
        (PiTensorProduct.tprod ℂ fun τ => b τ (v τ)) = E.coord k := by
      apply E.ext
      intro j
      simp only [hv, E, Basis.piTensorProduct_apply, PiTensorProduct.dualDistrib_apply,
        Basis.coord_apply, Basis.repr_self]
      rw [← Basis.piTensorProduct_apply, Basis.repr_self]
      simp only [Finsupp.single_apply]
      by_cases hjk : j = k
      · subst hjk; simp
      · rw [if_neg hjk]
        obtain ⟨τ, hτ⟩ : ∃ τ, j τ ≠ k τ := by
          by_contra h; push_neg at h; exact hjk (funext h)
        exact Finset.prod_eq_zero (Finset.mem_univ τ) (if_neg hτ)
    simpa [key] using hk

end GlobalTheory
