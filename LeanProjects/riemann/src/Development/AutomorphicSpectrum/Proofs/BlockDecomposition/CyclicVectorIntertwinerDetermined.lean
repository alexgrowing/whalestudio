import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableMulInner

noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods GlobalTheory.CompanionTheory.RgHeA
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA

theorem lower_bound_of_cyclic_coef : ∀ {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
    [InnerProductSpace ℂ B] [CompleteSpace B] (σ : Γ → (A →L[ℂ] A)) (ρ : Γ → (B →L[ℂ] B)) (d : ℝ), 0 < d → IsU σ → IsU ρ →
    ∀ (w₀ : A) (v : B) (i : A →L[ℂ] B), IsMap σ ρ i → (Submodule.span ℂ (Set.range fun x => σ x w₀)).topologicalClosure = ⊤ →
    ∀ (T : A →L[ℂ] A) (E : B →L[ℂ] B), (∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = star ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ) →
    (∀ z, ‖⟪z, i w₀⟫_ℂ‖ ^ 2 / d ≤ (⟪z, E z⟫_ℂ).re) → ∀ a, ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re := by
  intro Γ _ _ A B _ _ _ _ _ _ σ ρ d hd hσ hρ w₀ v i hi hcyc T E hTE hE a
  obtain ⟨h1, hmul, hnorm, -⟩ := hρ
  have hρinner : ∀ (g : Γ) (x y : B), ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ := fun g x y =>
    (LinearIsometry.mk (ρ g : B →ₗ[ℂ] B) (hnorm g)).inner_map_map x y
  have hadj : ∀ (g : Γ) (x y : B), ⟪ρ g⁻¹ x, y⟫_ℂ = ⟪x, ρ g y⟫_ℂ := by
    intro g x y
    rw [← hρinner g (ρ g⁻¹ x) y]
    congr 1
    rw [← ContinuousLinearMap.mul_apply, ← hmul, mul_inv_cancel, h1, ContinuousLinearMap.one_apply]
  have hi' : ∀ (g : Γ) (x : A), i (σ g x) = ρ g (i x) := hi
  have hTE' : ∀ x y, ⟪σ x w₀, T (σ y w₀)⟫_ℂ = starRingEnd ℂ ⟪ρ x⁻¹ v, E (ρ y⁻¹ v)⟫_ℂ :=
    fun x y => (hTE x y).trans (starRingEnd_apply _).symm
  have hclosed : IsClosed {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    apply isClosed_le
    · exact ((continuous_const.inner i.continuous).norm.pow 2).div_const d
    · exact Complex.continuous_re.comp (continuous_id.inner T.continuous)
  have hspan : (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) ⊆
      {a : A | ‖⟪v, i a⟫_ℂ‖ ^ 2 / d ≤ (⟪a, T a⟫_ℂ).re} := by
    intro a ha
    rw [SetLike.mem_coe, Finsupp.mem_span_range_iff_exists_finsupp] at ha
    obtain ⟨c, rfl⟩ := ha
    set z : B := c.sum fun y t => starRingEnd ℂ t • ρ y⁻¹ v with hz
    have h1' : ⟪v, i (c.sum fun x t => t • σ x w₀)⟫_ℂ = ⟪z, i w₀⟫_ℂ := by
      rw [hz]
      simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
        inner_smul_left, hi', hadj, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    have h2' : ⟪c.sum fun x t => t • σ x w₀, T (c.sum fun x t => t • σ x w₀)⟫_ℂ =
        starRingEnd ℂ ⟪z, E z⟫_ℂ := by
      rw [hz]
      simp only [Finsupp.sum, map_sum, map_smul, inner_sum, sum_inner, inner_smul_right,
        inner_smul_left, hTE', map_mul, Complex.conj_conj, RCLike.conj_conj, starRingEnd_self_apply]
    rw [Set.mem_setOf_eq, h1', h2', Complex.conj_re]
    exact hE z
  have ha : a ∈ closure (Submodule.span ℂ (Set.range fun x => σ x w₀) : Set A) := by
    rw [← Submodule.topologicalClosure_coe, hcyc]
    simp
  exact closure_minimal hspan hclosed ha

end GlobalTheory.CompanionTheory.RgHeA
