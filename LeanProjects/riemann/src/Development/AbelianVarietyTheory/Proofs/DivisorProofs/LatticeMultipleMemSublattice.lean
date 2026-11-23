import Mathlib

open Module

namespace GlobalTheory

theorem sublattice_of_full_rank_quotient_torsion : ∀ (n : ℕ) (Λ Λ₂ M : Submodule ℤ (Fin n → ℂ)), DiscreteTopology Λ → DiscreteTopology Λ₂ → Submodule.span ℝ (Λ : Set (Fin n → ℂ)) = ⊤ → Submodule.span ℝ (Λ₂ : Set (Fin n → ℂ)) = ⊤ → M ≤ Λ → Module.rank ℤ Λ₂ ≤ Module.rank ℤ M → ∀ w ∈ Λ, ∃ k : ℤ, k ≠ 0 ∧ k • w ∈ M := by
  intro n Λ Λ₂ M hΛ hΛ₂ hsΛ hsΛ₂ hM hr w hw
  haveI : IsZLattice ℝ Λ := ⟨hsΛ⟩
  haveI : IsZLattice ℝ Λ₂ := ⟨hsΛ₂⟩
  haveI : Module.Finite ℤ Λ := ZLattice.module_finite ℝ Λ
  haveI : Module.Finite ℤ Λ₂ := ZLattice.module_finite ℝ Λ₂
  have e1 : finrank ℤ Λ = finrank ℝ (Fin n → ℂ) := ZLattice.rank ℝ Λ
  have e2 : finrank ℤ Λ₂ = finrank ℝ (Fin n → ℂ) := ZLattice.rank ℝ Λ₂
  set M' : Submodule ℤ Λ := M.comap Λ.subtype with hM'
  have hMM : Module.rank ℤ M' = Module.rank ℤ M := (Submodule.comapSubtypeEquivOfLe hM).rank_eq
  have hΛr : Module.rank ℤ Λ = (finrank ℤ Λ : Cardinal) := (Module.finrank_eq_rank ℤ Λ).symm
  have hΛ₂r : Module.rank ℤ Λ₂ = (finrank ℤ Λ₂ : Cardinal) := (Module.finrank_eq_rank ℤ Λ₂).symm
  have hle : Module.rank ℤ M' ≤ Module.rank ℤ Λ := Submodule.rank_le M'
  have hge : Module.rank ℤ Λ ≤ Module.rank ℤ M' := by
    rw [hMM, hΛr, e1, ← e2, ← hΛ₂r]; exact hr
  have heq : Module.rank ℤ M' = Module.rank ℤ Λ := le_antisymm hle hge
  have hsum := rank_quotient_add_rank_of_isDomain M'
  haveI : Module.Finite ℤ M' := Module.Finite.of_injective M'.subtype M'.injective_subtype
  rw [heq, hΛr, ← Module.finrank_eq_rank ℤ (Λ ⧸ M')] at hsum
  have h0 : finrank ℤ (Λ ⧸ M') = 0 := by
    have : ((finrank ℤ (Λ ⧸ M') + finrank ℤ Λ : ℕ) : Cardinal) = (finrank ℤ Λ : Cardinal) := by
      push_cast; exact hsum
    have := Nat.cast_injective this
    omega
  have htor : Module.IsTorsion ℤ (Λ ⧸ M') := Module.finrank_eq_zero_iff_isTorsion.1 h0
  obtain ⟨⟨k, hk⟩, hx⟩ := htor (x := Submodule.Quotient.mk (⟨w, hw⟩ : Λ))
  refine ⟨k, nonZeroDivisors.ne_zero hk, ?_⟩
  have : (k • (⟨w, hw⟩ : Λ)) ∈ M' := by
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]; exact hx
  simpa [hM'] using this

end GlobalTheory
