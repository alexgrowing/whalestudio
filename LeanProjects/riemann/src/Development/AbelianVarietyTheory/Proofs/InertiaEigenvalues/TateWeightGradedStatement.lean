import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateWeightGraded
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.filter_weight_mem_of_tate_graded_stable : ∀ {C σ Γ : Type} [Field C] [Group Γ] [MulSemiringAction Γ C] (χ : Γ →* Cˣ), (∀ m : ℤ, m ≠ 0 → ∀ a : C, (∀ g : Γ, g • a = ((χ g ^ m : Cˣ) : C) * a) → a = 0) → ∀ (w : σ → ℤ) (J : Submodule C (σ →₀ C)), (∀ g : Γ, ∀ φ ∈ J, ∃ ψ ∈ J, ∀ m, ψ m = ((χ g ^ w m : Cˣ) : C) * (g • φ m)) → ∀ φ ∈ J, ∀ d : ℤ, φ.filter (fun m => w m = d) ∈ J := by
  first | exact @GlobalTheory.tate_weight_graded | exact GlobalTheory.tate_weight_graded | (intros; apply GlobalTheory.tate_weight_graded <;> assumption)
