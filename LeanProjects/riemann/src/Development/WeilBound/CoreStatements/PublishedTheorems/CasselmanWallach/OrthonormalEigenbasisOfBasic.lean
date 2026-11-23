import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirAlgebra.MulMulSubMulMulEqAdd

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenvectorBasisSetup

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

theorem casK_apply (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimirK ε E v = ∑ a, ∑ b, if ε b = ε a then E a b (E b a v) else 0 := by
  unfold casimirK
  simp only [Finset.sum_filter, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs <;> simp

theorem cas_apply (E : Fin n → Fin n → Module.End ℂ V) (v : V) :
    casimir E v = ∑ a, ∑ b, E a b (E b a v) := by
  unfold casimir
  simp [LinearMap.sum_apply]

theorem nc_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f : Fin n × Fin n → M) :
    ∑ p ∈ nc ε, f p = ∑ a, ∑ b, if ε b = ε a then 0 else f (a, b) := by
  unfold nc
  rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem swap_sum {M : Type*} [AddCommMonoid M] (ε : Fin n → Bool) (f g : Fin n → Fin n → M) :
    (∑ a, ∑ b, if ε b = ε a then f a b else g a b) =
      ∑ a, ∑ b, if ε b = ε a then f b a else g b a := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : ε b = ε a
  · simp [h]
  · have : ε a ≠ ε b := fun h' => h h'.symm
    simp [h, this]

theorem sq_re (u : V) : ‖u‖ ^ 2 = (inner ℂ u u).re := by
  simpa using (inner_self_eq_norm_sq (𝕜 := ℂ) u).symm

theorem sm_re (r : ℝ) (u : V) : (inner ℂ u ((r : ℂ) • u)).re = r * ‖u‖ ^ 2 := by
  rw [inner_smul_right, Complex.re_ofReal_mul, ← sq_re]

end EigenvectorBasisSetup

open EigenvectorBasisSetup in
theorem orthonormal_eigenbasis_of_basic : A0 := by
  intro n ε V _ _ E hM
  have hU := hM.uni
  have hc : ∀ a b, ε b = ε a → ∀ x y, inner ℂ (E a b x) y = inner ℂ x (E b a y) := by
    intro a b h x y
    rw [hU a b x y]
    simp [adjSign, h.symm]
  have hK : ∀ x y, inner ℂ x (casimirK ε E y) =
      ∑ a, ∑ b, if ε b = ε a then inner ℂ (E b a x) (E b a y) else 0 := by
    intro x y
    rw [casK_apply, inner_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [inner_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs with h
    · rw [hc b a h.symm]
    · simp
  have hKre : ∀ w, (inner ℂ w (casimirK ε E w)).re =
      ∑ a, ∑ b, if ε b = ε a then ‖E b a w‖ ^ 2 else 0 := by
    intro w
    rw [hK, Complex.re_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs
    · rw [sq_re]
    · simp
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    rw [← inner_conj_symm, hK, hK, map_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> simp
  · intro μ v hv h0
    have h1 := hKre v
    rw [hv, sm_re] at h1
    have h2 : 0 ≤ μ * ‖v‖ ^ 2 := by
      rw [h1]
      refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
      split_ifs <;> positivity
    have h3 : 0 < ‖v‖ ^ 2 := by positivity
    exact nonneg_of_mul_nonneg_left h2 h3
  · intro a b h
    unfold Z
    exact sub_eq_zero.mpr (casimirK_comm ε hM.gl a b h)
  · intro κ hκ w
    have h3 : ∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w) = (κ : ℂ) • w - casimirK ε E w := by
      rw [← hκ w, cas_apply, casK_apply, nc_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs <;> simp
    have hnorm : ∀ a b, ‖E a b w‖ ^ 2 = (adjSign ε a b * inner ℂ w (E b a (E a b w))).re := by
      intro a b
      rw [sq_re, hU]
    have h2 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 = (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 =
          ∑ a, ∑ b, if ε b = ε a then 0 else -(inner ℂ w (E b a (E a b w))).re := by
        rw [nc_sum]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        by_cases h : ε b = ε a
        · simp [h]
        · have : ε a ≠ ε b := fun h' => h h'.symm
          simp [h, hnorm, adjSign, this]
      have e2 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else -(inner ℂ w (E b a (E a b w))).re) =
          -(inner ℂ w (∑ p ∈ nc ε, E p.1 p.2 (E p.2 p.1 w))).re := by
        rw [swap_sum, nc_sum, inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [inner_sum, Complex.re_sum, ← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      rw [e1, e2, h3, inner_sub_right, Complex.sub_re, sm_re]
      ring
    have h1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 = 2 * (inner ℂ w (casimirK ε E w)).re - κ * ‖w‖ ^ 2 := by
      have e1 : ∑ a, ∑ b, ‖E a b w‖ ^ 2 =
          (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else 0) +
            ∑ a, ∑ b, if ε b = ε a then 0 else ‖E a b w‖ ^ 2 := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun b _ => ?_
        split_ifs <;> simp
      have e2 : (∑ a, ∑ b, if ε b = ε a then ‖E a b w‖ ^ 2 else (0 : ℝ)) =
          (inner ℂ w (casimirK ε E w)).re := by
        rw [hKre, swap_sum]
      have e3 : (∑ a, ∑ b, if ε b = ε a then (0 : ℝ) else ‖E a b w‖ ^ 2) =
          ∑ p ∈ nc ε, ‖E p.1 p.2 w‖ ^ 2 := by
        rw [nc_sum]
      rw [e1, e2, e3, h2]
      ring
    exact ⟨h1, h2, h3⟩

end PositivityTheory.CW

end
