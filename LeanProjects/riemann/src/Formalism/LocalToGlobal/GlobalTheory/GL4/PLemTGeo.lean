import Mathlib
import Formalism.PeriodIntegrals.Transference
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TransferenceCover

noncomputable section

open Module
open scoped InnerProductSpace

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT

theorem span_short_of_cover {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) (μ : ℝ) (hμ : 0 < μ) (hcov : ∀ x : W, ∃ l ∈ Λ, ‖x - l‖ ≤ μ) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ} = ⊤ := by
  set K := Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * μ} with hK
  by_contra hne
  have hKo : Kᗮ ≠ ⊥ := by
    intro h
    exact hne (Submodule.orthogonal_eq_bot_iff.mp h)
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKo
  have hun : 0 < ‖u‖ := norm_pos_iff.mpr hu0
  set x : W := (2 * μ / ‖u‖) • u with hx
  have hxn : ‖x‖ = 2 * μ := by
    rw [hx, norm_smul, Real.norm_of_nonneg (by positivity)]
    field_simp
  have hxK : x ∈ Kᗮ := Submodule.smul_mem _ _ hu
  obtain ⟨l, hl, hd⟩ := hcov x
  have hln : ‖l‖ ≤ 3 * μ := by
    have : ‖l‖ ≤ ‖x‖ + ‖x - l‖ := by
      calc ‖l‖ = ‖x - (x - l)‖ := by congr 1; abel
        _ ≤ ‖x‖ + ‖x - l‖ := norm_sub_le _ _
    linarith
  have hlK : l ∈ K := Submodule.subset_span ⟨hl, hln⟩
  have horth : ⟪l, x⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hlK hxK
  have hsq : ‖x - l‖ ^ 2 = ‖x‖ ^ 2 + ‖l‖ ^ 2 := by
    rw [@norm_sub_sq_real, real_inner_comm, horth]
    ring
  have h1 : ‖x - l‖ ^ 2 ≤ μ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hd 2
  nlinarith [sq_nonneg ‖l‖]

theorem span_short_of_dual {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (Λ : Submodule ℤ W) [DiscreteTopology Λ] [IsZLattice ℝ Λ] (lam : ℝ) (hlam : 0 < lam)
    (hd : ∀ y : W, y ≠ 0 → (∀ x ∈ Λ, ∃ n : ℤ, ⟪x, y⟫_ℝ = (n : ℝ)) → lam ≤ ‖y‖) :
    Submodule.span ℝ {l : W | l ∈ Λ ∧ ‖l‖ ≤ 3 * ((finrank ℝ W : ℝ) / 2 / lam + 1)} = ⊤ := by
  have hμ : 0 < (finrank ℝ W : ℝ) / 2 / lam + 1 := by positivity
  refine span_short_of_cover Λ _ hμ fun x ↦ ?_
  obtain ⟨l, hl, hle⟩ := transference_covering W Λ lam hlam hd x
  refine ⟨l, hl, ?_⟩
  rw [← le_div_iff₀ hlam] at hle
  have : (finrank ℝ W : ℝ) / 2 / lam = (finrank ℝ W : ℝ) / 2 / lam := rfl
  linarith

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality.LT
