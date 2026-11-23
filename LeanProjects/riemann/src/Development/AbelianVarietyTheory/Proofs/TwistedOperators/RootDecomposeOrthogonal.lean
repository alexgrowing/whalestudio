import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.InverseChamberMap
open GlobalTheory.Chamber
open scoped InnerProductSpace ContDiff Classical

namespace GlobalTheory.Chamber

variable {k : ℕ}

theorem rtStep_vec_mem {P : Finset (SV k)} {w : SV k} (h : w ∈ P) : vec w ∈ aP P :=
  Submodule.subset_span ⟨w, h, rfl⟩

theorem rtStep_inner_wt {Q : Finset (SV k)} (w : SV k) {a : A0 k} (ha : a ∈ aP Q) : ⟪wt Q w, a⟫_ℝ = 0 :=
  Submodule.inner_left_of_mem_orthogonal ha (Submodule.sub_starProjection_mem_orthogonal _)

theorem rtStep_wt_mem {P Q : Finset (SV k)} (e : Q ⊆ P) {w : SV k} (h : w ∈ P) : wt Q w ∈ aP P :=
  sub_mem (rtStep_vec_mem h) (vecSpan_mono e (Submodule.starProjection_apply_mem _ _))

theorem rtStep_orth {P : Finset (SV k)} {r : A0 k} (h : ∀ w ∈ P, ⟪r, vec w⟫_ℝ = 0) {a : A0 k} (ha : a ∈ aP P) :
    ⟪r, a⟫_ℝ = 0 := by
  have : aP P ≤ (ℝ ∙ r)ᗮ := Submodule.span_le.2 (by
    rintro _ ⟨w, hw, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_right.2 (h w hw))
  exact Submodule.mem_orthogonal_singleton_iff_inner_right.1 (this ha)

theorem rt_eq_smul_rt_erase_add {T : Finset (SV k)} {u v : SV k} (hT : IsPar T) (hu : u ∈ T) (hv : v ∈ T)
    (hvu : v ≠ u) : ∃ κ : ℝ, 0 < κ ∧ ∃ t : ℝ,
      rt T v = κ • rt (T.erase u) v + t • rt T u ∧ ⟪rt (T.erase u) v, rt T u⟫_ℝ = 0 := by
  have hvS : v ∈ T.erase u := Finset.mem_erase.2 ⟨hvu, hv⟩
  have huB : u ∈ T.erase v := Finset.mem_erase.2 ⟨hvu.symm, hu⟩
  have hAB : (T.erase u).erase v ⊆ T.erase v := fun w hw =>
    Finset.mem_erase.2 ⟨Finset.ne_of_mem_erase hw, Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hw)⟩
  have hAC : (T.erase u).erase v ⊆ T.erase u := Finset.erase_subset _ _

  have hyC : rt (T.erase u) v ∈ aP (T.erase u) := rtStep_wt_mem hAC hvS
  have hzC : ∀ a ∈ aP (T.erase u), ⟪rt T u, a⟫_ℝ = 0 := fun a ha => rtStep_inner_wt u ha
  have hyz : ⟪rt (T.erase u) v, rt T u⟫_ℝ = 0 := by rw [real_inner_comm]; exact hzC _ hyC
  have hxB : ∀ a ∈ aP (T.erase v), ⟪rt T v, a⟫_ℝ = 0 := fun a ha => rtStep_inner_wt v ha
  have hxA : ∀ a ∈ aP ((T.erase u).erase v), ⟪rt T v, a⟫_ℝ = 0 := fun a ha => hxB a (vecSpan_mono hAB ha)
  have hyA : ∀ a ∈ aP ((T.erase u).erase v), ⟪rt (T.erase u) v, a⟫_ℝ = 0 := fun a ha => rtStep_inner_wt v ha
  have hzA : ∀ a ∈ aP ((T.erase u).erase v), ⟪rt T u, a⟫_ℝ = 0 := fun a ha => hzC a (vecSpan_mono hAC ha)
  have hx0 : rt T v ≠ 0 := hT.wt_ne_zero (Finset.erase_subset v T) (by simp [hv])
  have hz0 : rt T u ≠ 0 := hT.wt_ne_zero (Finset.erase_subset u T) (by simp [hu])

  have hxy : ⟪rt T v, rt (T.erase u) v⟫_ℝ = ⟪rt T v, rt T v⟫_ℝ := by
    have hd : rt (T.erase u) v - rt T v ∈ aP (T.erase v) := by
      have : rt (T.erase u) v - rt T v =
          pr (T.erase v) (vec v) - pr ((T.erase u).erase v) (vec v) := by
        simp only [rt, wt]; abel
      rw [this]
      exact sub_mem (Submodule.starProjection_apply_mem _ _) (vecSpan_mono hAB (Submodule.starProjection_apply_mem _ _))
    have := hxB _ hd
    rw [inner_sub_right, sub_eq_zero] at this
    exact this
  have hxx : 0 < ⟪rt T v, rt T v⟫_ℝ := real_inner_self_pos.2 hx0
  have hyy : ⟪rt (T.erase u) v, rt (T.erase u) v⟫_ℝ ≠ 0 := by
    intro h0
    have : rt (T.erase u) v = 0 := inner_self_eq_zero.1 h0
    rw [this, inner_zero_right] at hxy
    exact hxx.ne hxy
  have hzz : ⟪rt T u, rt T u⟫_ℝ ≠ 0 := fun h0 => hz0 (inner_self_eq_zero.1 h0)
  have hyy' : 0 < ⟪rt (T.erase u) v, rt (T.erase u) v⟫_ℝ := lt_of_le_of_ne real_inner_self_nonneg (Ne.symm hyy)
  refine ⟨⟪rt T v, rt (T.erase u) v⟫_ℝ / ⟪rt (T.erase u) v, rt (T.erase u) v⟫_ℝ, div_pos (hxy ▸ hxx) hyy',
    ⟪rt T v, rt T u⟫_ℝ / ⟪rt T u, rt T u⟫_ℝ, ?_, hyz⟩
  set κ := ⟪rt T v, rt (T.erase u) v⟫_ℝ / ⟪rt (T.erase u) v, rt (T.erase u) v⟫_ℝ with hκ
  set t := ⟪rt T v, rt T u⟫_ℝ / ⟪rt T u, rt T u⟫_ℝ with ht
  set r := rt T v - κ • rt (T.erase u) v - t • rt T u with hr
  have hry : ⟪r, rt (T.erase u) v⟫_ℝ = 0 := by
    rw [hr, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left,
      real_inner_comm (rt (T.erase u) v) (rt T u), hyz,
      hκ]
    field_simp
    ring
  have hrz : ⟪r, rt T u⟫_ℝ = 0 := by
    rw [hr, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hyz, ht]
    field_simp
    ring
  have hrA : ∀ a ∈ aP ((T.erase u).erase v), ⟪r, a⟫_ℝ = 0 := fun a ha => by
    rw [hr, inner_sub_left, inner_sub_left, real_inner_smul_left, real_inner_smul_left, hxA a ha, hyA a ha, hzA a ha]
    ring
  have hrC : ∀ a ∈ aP (T.erase u), ⟪r, a⟫_ℝ = 0 := fun a ha => by
    refine rtStep_orth (fun w hw => ?_) ha
    by_cases hwv : w = v
    · subst hwv
      have : vec w = rt (T.erase u) w + pr ((T.erase u).erase w) (vec w) := by simp [rt, wt]
      rw [this, inner_add_right, hry, hrA (pr ((T.erase u).erase w) (vec w)) (Submodule.starProjection_apply_mem _ _), add_zero]
    · exact hrA _ (rtStep_vec_mem (Finset.mem_erase.2 ⟨hwv, hw⟩))
  have hrT : ∀ a ∈ aP T, ⟪r, a⟫_ℝ = 0 := fun a ha => by
    refine rtStep_orth (fun w hw => ?_) ha
    by_cases hwu : w = u
    · subst hwu
      have : vec w = rt T w + pr (T.erase w) (vec w) := by simp [rt, wt]
      rw [this, inner_add_right, hrz, hrC (pr (T.erase w) (vec w)) (Submodule.starProjection_apply_mem _ _), add_zero]
    · exact hrC _ (rtStep_vec_mem (Finset.mem_erase.2 ⟨hwu, hw⟩))
  have hrm : r ∈ aP T := by
    rw [hr]
    refine sub_mem (sub_mem (rtStep_wt_mem (Finset.erase_subset v T) hv) (Submodule.smul_mem _ _
      (vecSpan_mono (Finset.erase_subset u T) hyC))) (Submodule.smul_mem _ _ (rtStep_wt_mem (Finset.erase_subset u T) hu))
  have h0 : r = 0 := inner_self_eq_zero.1 (hrT r hrm)
  rw [hr, sub_sub, sub_eq_zero] at h0
  exact h0

end GlobalTheory.Chamber
