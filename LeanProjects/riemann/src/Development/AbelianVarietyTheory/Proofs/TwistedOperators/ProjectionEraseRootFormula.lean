import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory

theorem pr_eq_pr_erase_add_rt : ∀ {k : ℕ} {T : Finset (SV k)} {u : SV k}, IsPar T → u ∈ T → ∀ x : A0 k,
    pr T x = pr (T.erase u) x + (⟪rt T u, x⟫_ℝ / ‖rt T u‖ ^ 2) • rt T u := by
  intro k T u hT hu x
  set E := aP (T.erase u) with hE
  set r := rt T u with hr
  have hEK : E ≤ aP T := vecSpan_mono (Finset.erase_subset _ _)
  have hvu : vec u ∈ aP T := Submodule.subset_span ⟨u, hu, rfl⟩
  have hrdef : r = vec u - E.starProjection (vec u) := rfl
  have hrE : r ∈ Eᗮ := by rw [hrdef]; exact Submodule.sub_starProjection_mem_orthogonal _
  have hrK : r ∈ aP T := by
    rw [hrdef]; exact sub_mem hvu (hEK (Submodule.starProjection_apply_mem _ _))
  have hr0 : r ≠ 0 := hT.wt_ne_zero (Finset.erase_subset u T) (by simp [hu])
  have hn : ‖r‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.2 hr0)
  set c := ⟪r, x⟫_ℝ / ‖r‖ ^ 2 with hc
  have hxyE : x - (pr (T.erase u) x + c • r) ∈ Eᗮ := by
    rw [← sub_sub]
    exact sub_mem (Submodule.sub_starProjection_mem_orthogonal _) (Submodule.smul_mem _ _ hrE)
  have hxyr : ⟪x - (pr (T.erase u) x + c • r), r⟫_ℝ = 0 := by
    have h1 : ⟪pr (T.erase u) x, r⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hrE
    rw [inner_sub_left, inner_add_left, h1, inner_smul_left, real_inner_self_eq_norm_sq, real_inner_comm, hc]
    simp only [conj_trivial]
    field_simp
    ring
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    (add_mem (hEK (Submodule.starProjection_apply_mem _ _)) (Submodule.smul_mem _ _ hrK)) ?_
  intro w hw
  have hle : aP T ≤ (ℝ ∙ (x - (pr (T.erase u) x + c • r)))ᗮ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨v, hv, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_orthogonal_singleton_iff_inner_right]
    by_cases hvu' : v = u
    · subst hvu'
      have : vec v = r + E.starProjection (vec v) := by rw [hrdef]; abel
      rw [this, inner_add_right, hxyr, zero_add, real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hxyE
    · rw [real_inner_comm]
      have hvE : vec v ∈ E := Submodule.subset_span ⟨v, Finset.mem_coe.2 (Finset.mem_erase.2 ⟨hvu', hv⟩), rfl⟩
      exact Submodule.inner_right_of_mem_orthogonal hvE hxyE
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (hle hw)

end GlobalTheory
