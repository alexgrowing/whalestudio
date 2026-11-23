import Mathlib
open scoped InnerProductSpace

namespace GlobalTheory

theorem mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts
    {X Y ι : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y]
    (T : X →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ) (hP : (⨆ k, P k) = ⊤)
    (hl : ∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) (u : Y) :
    m * ‖u‖ ^ 2 ≤ ‖LinearMap.adjoint T u‖ ^ 2 := by
  by_cases hu : u = 0
  · simp [hu]
  haveI : Nontrivial Y := ⟨⟨u, 0, hu⟩⟩
  set S : Y →ₗ[ℂ] Y := T ∘ₗ LinearMap.adjoint T with hS
  have hsym : S.IsSymmetric := by
    intro a b
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, LinearMap.adjoint_inner_left]
  have hq : ∀ y : Y, RCLike.re ⟪S y, y⟫_ℂ = ‖LinearMap.adjoint T y‖ ^ 2 := by
    intro y
    simp only [hS, LinearMap.comp_apply]
    rw [← LinearMap.adjoint_inner_right T, inner_self_eq_norm_sq]
  have hev : ∀ μ : ℝ, Module.End.HasEigenvalue S (μ : ℂ) → m ≤ μ := by
    intro μ hμ
    obtain ⟨v, hv⟩ := hμ.exists_hasEigenvector
    by_contra hlt
    have hlt : μ < m := not_le.mp hlt
    have hSv : S v = (μ : ℂ) • v := hv.apply_eq_smul
    have hle : ∀ k, P k ≤ (ℂ ∙ v)ᗮ := by
      intro k y hy
      obtain ⟨l, hml, hly⟩ := hl k
      rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
      have h1 := hsym v y
      have h2 : S y = (l : ℂ) • y := hly y hy
      rw [hSv, h2, inner_smul_left, inner_smul_right, Complex.conj_ofReal] at h1
      have h3 : ((μ : ℂ) - (l : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        intro h
        have : μ = l := by exact_mod_cast h
        linarith
      have h4 : ((μ : ℂ) - (l : ℂ)) * ⟪v, y⟫_ℂ = 0 := by rw [sub_mul, h1, sub_self]
      exact (mul_eq_zero.mp h4).resolve_left h3
    have hv' : v ∈ (ℂ ∙ v)ᗮ := by
      have : (⊤ : Submodule ℂ Y) ≤ (ℂ ∙ v)ᗮ := hP ▸ iSup_le hle
      exact this Submodule.mem_top
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right, inner_self_eq_zero] at hv'
    exact hv.2 hv'
  have h1 := hev _ hsym.hasEigenvalue_iInf_of_finiteDimensional
  have hb : BddBelow (Set.range fun x : { x : Y // x ≠ 0 } =>
      RCLike.re ⟪S x, x⟫_ℂ / ‖(x : Y)‖ ^ 2) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨x, rfl⟩
    simp only [hq]
    positivity
  have h2 := h1.trans (ciInf_le hb ⟨u, hu⟩)
  simp only [hq] at h2
  have hpos : 0 < ‖u‖ ^ 2 := by positivity
  rwa [le_div_iff₀ hpos] at h2

theorem mul_norm_sq_le_norm_proj_apply_sq_of_spanning_parts :
    ∀ (X Y ι : Type) [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X] [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (T : X →ₗ[ℂ] Y) (e : Y →ₗ[ℂ] Y) (P : ι → Submodule ℂ Y) (m : ℝ), 0 < m → LinearMap.adjoint e = e → (∀ y, e (e y) = e y) → (⨆ k, P k) = ⊤ → (∀ k, ∃ l : ℝ, m ≤ l ∧ ∀ y ∈ P k, T (LinearMap.adjoint T y) = (l : ℂ) • y) → ∀ x ∈ (LinearMap.ker (e ∘ₗ T))ᗮ, m * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 := by
  intro X Y ι _ _ _ _ _ _ T e P m hm he hee hP hl x hx
  rw [LinearMap.orthogonal_ker] at hx
  obtain ⟨w, hw⟩ := hx
  rw [LinearMap.adjoint_comp, he, LinearMap.comp_apply] at hw
  set u := e w with hu
  have h1 := mul_norm_sq_le_norm_adjoint_sq_of_spanning_parts T P m hP hl u
  rw [hw] at h1
  have h2 : ⟪x, x⟫_ℂ = ⟪u, e (T x)⟫_ℂ := by
    have : ⟪u, e (T x)⟫_ℂ = ⟪e u, T x⟫_ℂ := by
      rw [← LinearMap.adjoint_inner_left e, he]
    rw [this, hu, hee, ← hu, ← LinearMap.adjoint_inner_left T, hw]
  have h3 : ‖x‖ ^ 2 ≤ ‖u‖ * ‖e (T x)‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) u (e (T x))
    rw [← h2, inner_self_eq_norm_sq_to_K] at h
    simpa using h
  by_cases hx0 : x = 0
  · simp [hx0]
  have hpos : 0 < ‖x‖ ^ 2 := by positivity
  have h4 : (‖x‖ ^ 2) ^ 2 ≤ (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
  have h5 : (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by
    calc (m * ‖x‖ ^ 2) * ‖x‖ ^ 2 = m * (‖x‖ ^ 2) ^ 2 := by ring
      _ ≤ m * (‖u‖ * ‖e (T x)‖) ^ 2 := by gcongr
      _ = ‖e (T x)‖ ^ 2 * (m * ‖u‖ ^ 2) := by ring
      _ ≤ ‖e (T x)‖ ^ 2 * ‖x‖ ^ 2 := by gcongr
  exact le_of_mul_le_mul_right h5 hpos

end GlobalTheory
