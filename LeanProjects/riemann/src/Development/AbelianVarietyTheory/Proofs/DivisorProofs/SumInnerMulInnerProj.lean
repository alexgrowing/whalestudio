import Mathlib

noncomputable section

open scoped InnerProductSpace

namespace GlobalTheory.Pc3

section
variable {U : Type} [NormedAddCommGroup U] [InnerProductSpace ℂ U] (L : Submodule ℂ U)
  [FiniteDimensional ℂ L]

theorem sum_inner_mul_inner_proj [L.HasOrthogonalProjection] (a c : U) :
    ∑ j, ⟪a, (stdOrthonormalBasis ℂ L j : U)⟫_ℂ * ⟪(stdOrthonormalBasis ℂ L j : U), c⟫_ℂ =
      ⟪a, c⟫_ℂ - ⟪a - L.starProjection a, c - L.starProjection c⟫_ℂ := by
  set e := stdOrthonormalBasis ℂ L
  have h1 : ∀ j, ⟪a, (e j : U)⟫_ℂ = ⟪(⟨L.starProjection a, L.starProjection_apply_mem a⟩ : L), e j⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right a (e j : U)
    rw [this, L.starProjection_eq_self_iff.2 (e j).2]
  have h2 : ∀ j, ⟪(e j : U), c⟫_ℂ = ⟪e j, (⟨L.starProjection c, L.starProjection_apply_mem c⟩ : L)⟫_ℂ := by
    intro j
    rw [Submodule.coe_inner]
    have := L.inner_starProjection_left_eq_right (e j : U) c
    rw [← this, L.starProjection_eq_self_iff.2 (e j).2]
  simp_rw [h1, h2]
  rw [e.sum_inner_mul_inner, Submodule.coe_inner]
  simp only
  have ha := L.sub_starProjection_mem_orthogonal a
  have hc := L.sub_starProjection_mem_orthogonal c
  have o1 : ⟪L.starProjection a, c - L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (L.starProjection_apply_mem a) hc
  have o2 : ⟪a - L.starProjection a, L.starProjection c⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (L.starProjection_apply_mem c) ha
  have e1 : ⟪a, c⟫_ℂ = ⟪L.starProjection a + (a - L.starProjection a),
      L.starProjection c + (c - L.starProjection c)⟫_ℂ := by simp
  rw [e1, inner_add_left, inner_add_right, inner_add_right, o1, o2]
  ring

end

theorem conjDeriv : ∀ (U : Type) [NormedAddCommGroup U] [InnerProductSpace ℂ U] [CompleteSpace U] (L : Submodule ℂ U) [FiniteDimensional ℂ L] (x y : ℝ → U →L[ℂ] U) (A : U →L[ℂ] U), x 0 = 1 → (∀ t v w, inner ℂ (x t v) (x t w) = inner ℂ v w) → (∀ t v w, inner ℂ v (y t w) = inner ℂ (x t v) w) → (∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v) w 0) → (∀ u, A u ∈ L) → (∀ u, ContinuousLinearMap.adjoint A u ∈ L) → HasDerivAt (fun t => ∑ j, inner ℂ (stdOrthonormalBasis ℂ L j : U) (x t (A (y t (stdOrthonormalBasis ℂ L j : U))))) 0 0 := by
  intro U _ _ _ L _ x y A hx0 hxi hy hxd hA hAd
  set e := stdOrthonormalBasis ℂ L
  set E : Fin (Module.finrank ℂ L) → U := fun j => (e j : U)
  set b : Fin (Module.finrank ℂ L) → U := fun k => ContinuousLinearMap.adjoint A (E k)

  have hexp : ∀ u, A u = ∑ k, ⟪E k, A u⟫_ℂ • E k := by
    intro u
    have := e.sum_repr' (⟨A u, hA u⟩ : L)
    have h := congrArg (fun z : L => (z : U)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul, Submodule.coe_inner] at h
    exact h.symm
  have hterm : ∀ t, (∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) =
      ∑ k, (⟪x t (b k), x t (E k)⟫_ℂ - ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ) := by
    intro t
    have h1 : ∀ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ = ∑ k, ⟪x t (b k), E j⟫_ℂ * ⟪E j, x t (E k)⟫_ℂ := by
      intro j
      rw [hexp (y t (E j)), map_sum, inner_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left, hy]
    simp_rw [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    exact sum_inner_mul_inner_proj L _ _
  have hconst : ∀ t k, ⟪x t (b k), x t (E k)⟫_ℂ = ⟪b k, E k⟫_ℂ := fun t k => hxi t _ _
  simp_rw [hconst] at hterm
  have hfun : (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) = fun t =>
      (∑ k, ⟪b k, E k⟫_ℂ) - ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
        x t (E k) - L.starProjection (x t (E k))⟫_ℂ := by
    funext t; rw [hterm t, Finset.sum_sub_distrib]
  show HasDerivAt (fun t => ∑ j, ⟪E j, x t (A (y t (E j)))⟫_ℂ) 0 0
  rw [hfun]
  have hbL : ∀ k, b k ∈ L := fun k => hAd _
  have hEL : ∀ k, E k ∈ L := fun k => (e k).2
  have hd : ∀ v ∈ L, ∃ w, HasDerivAt (fun t => x t v - L.starProjection (x t v)) w 0 ∧
      x 0 v - L.starProjection (x 0 v) = 0 := by
    intro v hv
    obtain ⟨w, hw⟩ := hxd v hv
    have hP : HasDerivAt (fun t => L.starProjection (x t v)) (L.starProjection w) 0 :=
      (L.starProjection.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hw
    refine ⟨w - L.starProjection w, hw.sub hP, ?_⟩
    rw [hx0, ContinuousLinearMap.one_apply, L.starProjection_eq_self_iff.2 hv, sub_self]
  have hsum : HasDerivAt (fun t => ∑ k, ⟪x t (b k) - L.starProjection (x t (b k)),
      x t (E k) - L.starProjection (x t (E k))⟫_ℂ) 0 0 := by
    have : (0 : ℂ) = ∑ _k : Fin (Module.finrank ℂ L), (0 : ℂ) := by simp
    rw [this]
    refine HasDerivAt.fun_sum fun k _ => ?_
    obtain ⟨w1, h1, z1⟩ := hd _ (hbL k)
    obtain ⟨w2, h2, z2⟩ := hd _ (hEL k)
    have := h1.inner ℂ h2
    rw [z1, z2, inner_zero_left, inner_zero_right, add_zero] at this
    exact this
  have := hsum.const_sub (∑ k, ⟪b k, E k⟫_ℂ)
  rwa [neg_zero] at this

end GlobalTheory.Pc3
