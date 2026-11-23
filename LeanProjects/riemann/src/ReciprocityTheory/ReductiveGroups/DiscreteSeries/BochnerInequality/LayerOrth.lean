import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.LayerBasic
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.IsKUnitaryOfIsInfUnitary

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section LayerOrth

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M}

theorem isKHWVec_starProjection (hU : IsKUnitary ε E) {S : Submodule ℂ M}
    [S.HasOrthogonalProjection] (hS : IsKStableSub ε E S) {μ : Fin n → ℝ} {w : M}
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (S.starProjection w) := by
  have hcomm : ∀ a b, ε a = ε b → ∀ v, S.starProjection (E a b v) = E a b (S.starProjection v) := by
    intro a b hab v
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero (hS a b hab _ (S.starProjection_apply_mem v))
    intro u hu
    rw [← map_sub, hU a b hab]
    exact Submodule.inner_left_of_mem_orthogonal (hS b a hab.symm u hu)
      (Submodule.sub_starProjection_mem_orthogonal v)
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← hcomm a a rfl, hw.1 a, map_smul]
  · rw [← hcomm a b he, hw.2 a b hab he, map_zero]

theorem isKHWVec_sub {μ : Fin n → ℝ} {v w : M} (hv : IsKHWVec ε E μ v)
    (hw : IsKHWVec ε E μ w) : IsKHWVec ε E μ (v - w) := by
  refine ⟨fun a => ?_, fun a b h he => ?_⟩
  · rw [map_sub, hv.1 a, hw.1 a, smul_sub]
  · rw [map_sub, hv.2 a b h he, hw.2 a b h he, sub_zero]

theorem layer_khw_decomp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hVfd : FiniteDimensional ℂ V)
    (hVk : IsKStableSub ε E V) {k : ℕ} {w : M} (hw : w ∈ layer ε E V k) {μ : Fin n → ℝ}
    (hμ : IsKHWVec ε E μ w) :
    ∃ w₀ ∈ V, IsKHWVec ε E μ w₀ ∧ ∃ ws : Fin k → M, w = w₀ + ∑ j, ws j ∧
      ∀ j : Fin k, ws j ∈ layer ε E V ((j : ℕ) + 1) ∧
        (∀ u ∈ layer ε E V (j : ℕ), inner ℂ u (ws j) = 0) ∧ IsKHWVec ε E μ (ws j) := by
  have hKU : IsKUnitary ε E := by
    intro a b hab x y
    rw [hU a b x y]
    simp [adjSign, hab]
  have key : ∀ j : ℕ, ∃ p ∈ layer ε E V j, (∀ u ∈ layer ε E V j, inner ℂ u p = inner ℂ u w) ∧
      IsKHWVec ε E μ p ∧ (w ∈ layer ε E V j → p = w) := by
    intro j
    haveI := finiteDimensional_layer (ε := ε) (E := E) hVfd j
    refine ⟨(layer ε E V j).starProjection w, Submodule.starProjection_apply_mem _ _, ?_,
      isKHWVec_starProjection hKU (layer_kStable hE hVk j) hμ, ?_⟩
    · intro u hu
      rw [← Submodule.inner_starProjection_left_eq_right, Submodule.starProjection_eq_self_iff.mpr hu]
    · intro hw'
      exact Submodule.starProjection_eq_self_iff.mpr hw'
  choose P hP1 hP2 hP3 hP4 using key
  refine ⟨P 0, hP1 0, hP3 0, fun j => P ((j : ℕ) + 1) - P j, ?_, fun j => ⟨?_, ?_, ?_⟩⟩
  · rw [Fin.sum_univ_eq_sum_range (fun j => P (j + 1) - P j) k, Finset.sum_range_sub, hP4 k hw]
    abel
  · exact sub_mem (hP1 _) (layer_le_succ _ (hP1 _))
  · intro u hu
    rw [inner_sub_right, hP2 _ u (layer_le_succ _ hu), hP2 _ u hu, sub_self]
  · exact isKHWVec_sub (hP3 _) (hP3 _)

end LayerOrth

end ReciprocityTheory.ChartRestriction.DS
