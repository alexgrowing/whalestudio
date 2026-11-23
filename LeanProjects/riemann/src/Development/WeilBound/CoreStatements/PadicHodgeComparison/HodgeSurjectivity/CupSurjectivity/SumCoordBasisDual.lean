import Mathlib

namespace CrystallineSemistableComparison.Onto

theorem la_kill {K V U W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup U] [Module K U] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (g : U →ₗ[K] W) (Θ : Module.Dual K V) (h : ∀ C u, f C = g u → Θ C = 0) : ∃ φ : Module.Dual K W, φ ∘ₗ f = Θ ∧ φ ∘ₗ g = 0 := by
  let F : (V × U) →ₗ[K] W := f.coprod (-g)
  let Θ' : Module.Dual K (V × U) := Θ ∘ₗ LinearMap.fst K V U
  have hmem : Θ' ∈ (LinearMap.ker F).dualAnnihilator := by
    rw [Submodule.mem_dualAnnihilator]
    rintro ⟨C, u⟩ hx
    rw [LinearMap.mem_ker] at hx
    have hx' : f C + -g u = 0 := by simpa [F] using hx
    have hfg : f C = g u := by
      rw [← sub_eq_add_neg] at hx'
      exact sub_eq_zero.mp hx'
    simpa [Θ'] using h C u hfg
  rw [← LinearMap.range_dualMap_eq_dualAnnihilator_ker] at hmem
  obtain ⟨φ, hφ⟩ := hmem
  refine ⟨φ, ?_, ?_⟩
  · ext C
    have := congrArg (fun ψ : Module.Dual K (V × U) => ψ (C, 0)) hφ
    simpa [F, Θ', LinearMap.dualMap_apply] using this
  · ext u
    have := congrArg (fun ψ : Module.Dual K (V × U) => ψ (0, u)) hφ
    simpa [F, Θ', LinearMap.dualMap_apply] using this

theorem sum_coord_basis_dual {K C V : Type*} [Field K] [CommRing C] [AddCommGroup V] [Module K V] (κ : K →+* C) (h : Module.Dual K V →+ C) (l : ∀ (k : K) φ, h (k • φ) = κ k * h φ) {m : ℕ} (b : Module.Basis (Fin m) K V) (F : Module.Dual K V) : ∑ s, h (b.coord s) * κ (F (b s)) = h F := by
  conv_rhs => rw [← b.sum_dual_apply_smul_coord F]
  rw [map_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [l, mul_comm]

theorem gen2 {K C V₁ V₂ W₁ W₂ : Type*} [Field K] [CommRing C] [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂] [AddCommGroup W₁] [Module K W₁] [AddCommGroup W₂] [Module K W₂] (κ : K →+* C) (h₁ : Module.Dual K V₁ →+ C) (h₁' : Module.Dual K W₁ →+ C) (h₂ : Module.Dual K V₂ →+ C) (h₂' : Module.Dual K W₂ →+ C) (l₁ : ∀ (k : K) φ, h₁ (k • φ) = κ k * h₁ φ) (l₁' : ∀ (k : K) φ, h₁' (k • φ) = κ k * h₁' φ) (l₂ : ∀ (k : K) φ, h₂ (k • φ) = κ k * h₂ φ) (l₂' : ∀ (k : K) φ, h₂' (k • φ) = κ k * h₂' φ) (ι₁ : W₁ →ₗ[K] V₁) (ι₂ : W₂ →ₗ[K] V₂) (n₁ : ∀ F, h₁ F = h₁' (F ∘ₗ ι₁)) (n₂ : ∀ F, h₂ F = h₂' (F ∘ₗ ι₂)) (B : V₁ →ₗ[K] V₂ →ₗ[K] K) {m₁ m₂ k₁ k₂ : ℕ} (B₁ : Module.Basis (Fin m₁) K V₁) (B₂ : Module.Basis (Fin m₂) K V₂) (b₁ : Module.Basis (Fin k₁) K W₁) (b₂ : Module.Basis (Fin k₂) K W₂) : ∑ σ, ∑ σ', h₁ (B₁.coord σ) * h₂ (B₂.coord σ') * κ (B (B₁ σ) (B₂ σ')) = ∑ s, ∑ s', h₁' (b₁.coord s) * h₂' (b₂.coord s') * κ (B (ι₁ (b₁ s)) (ι₂ (b₂ s'))) := by
  calc ∑ σ, ∑ σ', h₁ (B₁.coord σ) * h₂ (B₂.coord σ') * κ (B (B₁ σ) (B₂ σ'))
      = ∑ σ, h₁ (B₁.coord σ) * h₂ (B (B₁ σ)) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [← sum_coord_basis_dual κ h₂ l₂ B₂ (B (B₁ σ)), Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ' _ => ?_
        ring
    _ = ∑ σ, ∑ s', h₁ (B₁.coord σ) * h₂' (b₂.coord s') * κ (B (B₁ σ) (ι₂ (b₂ s'))) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        rw [n₂, ← sum_coord_basis_dual κ h₂' l₂' b₂ (B (B₁ σ) ∘ₗ ι₂), Finset.mul_sum]
        refine Finset.sum_congr rfl fun s' _ => ?_
        simp only [LinearMap.comp_apply]
        ring
    _ = ∑ s', h₂' (b₂.coord s') * h₁ (B.flip (ι₂ (b₂ s'))) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [← sum_coord_basis_dual κ h₁ l₁ B₁ (B.flip (ι₂ (b₂ s'))), Finset.mul_sum]
        refine Finset.sum_congr rfl fun σ _ => ?_
        simp only [LinearMap.flip_apply]
        ring
    _ = ∑ s', ∑ s, h₁' (b₁.coord s) * h₂' (b₂.coord s') * κ (B (ι₁ (b₁ s)) (ι₂ (b₂ s'))) := by
        refine Finset.sum_congr rfl fun s' _ => ?_
        rw [n₁, ← sum_coord_basis_dual κ h₁' l₁' b₁ (B.flip (ι₂ (b₂ s')) ∘ₗ ι₁), Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [LinearMap.comp_apply, LinearMap.flip_apply]
        ring
    _ = ∑ s, ∑ s', h₁' (b₁.coord s) * h₂' (b₂.coord s') * κ (B (ι₁ (b₁ s)) (ι₂ (b₂ s'))) :=
        Finset.sum_comm

end CrystallineSemistableComparison.Onto
