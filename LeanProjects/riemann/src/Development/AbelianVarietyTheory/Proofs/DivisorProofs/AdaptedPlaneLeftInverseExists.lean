import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory

theorem plane_iota_leftInverse : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E), B.IsGood σ → ∀ (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁) (i₀ i₁ r s : ℕ),
    W.IsSkew σ B r s → H.IsAdapted σ B W W₁ i₀ i₁ → ∃ P : Matrix (Fin n₁) (Fin n) E, P * H.ι = 1 := by
  intro F E _ _ _ _ _ σ B _ n n₁ W W₁ H i₀ i₁ r s hW hH
  set f : (Fin n₁ → E) →ₗ[E] (Fin n → E) := Matrix.toLin' H.ι with hf
  have htop : Submodule.span E {H.x} ⊔ Submodule.span E {H.y} ⊔ LinearMap.range f = ⊤ := by
    have hl := hW.lat
    rw [eq_top_iff, ← hl.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hH.split z hz
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_right ⟨u, by simp [hf, Matrix.toLin'_apply]⟩
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  have h1 : ∀ v : Fin n → E, Module.finrank E (Submodule.span E {v}) ≤ 1 := fun v => by
    simpa using finrank_span_le_card ({v} : Set (Fin n → E))
  have hle : n ≤ 1 + 1 + Module.finrank E (LinearMap.range f) := by
    have e1 := Submodule.finrank_add_le_finrank_add_finrank
      (Submodule.span E {H.x} ⊔ Submodule.span E {H.y}) (LinearMap.range f)
    have e2 := Submodule.finrank_add_le_finrank_add_finrank (Submodule.span E {H.x}) (Submodule.span E {H.y})
    rw [htop, finrank_top, Module.finrank_fin_fun] at e1
    have := h1 H.x
    have := h1 H.y
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker f
  rw [Module.finrank_fin_fun] at hrk
  have hker : LinearMap.ker f = ⊥ := by
    apply Submodule.finrank_eq_zero.mp
    have := hH.rank
    omega
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective f hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have : H.ι = LinearMap.toMatrix' f := by simp [hf]
  rw [this, ← LinearMap.toMatrix'_comp, hg, LinearMap.toMatrix'_id]

end GlobalTheory
