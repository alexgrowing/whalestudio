import ReciprocityTheory.ReductiveGroups.DiscreteSeries.BochnerInequality.CrossOpSlotBound
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.StdGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.NcVOneDecomp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.CrossOpEigGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.ExceptionalGroupG2.BochnerG2.Numerics

noncomputable section

open Finset

namespace ReciprocityTheory.ChartRestriction.DS.G2
variable {n : ℕ}

section Slot

variable {M : Type*} [NormedAddCommGroup M] [InnerProductSpace ℂ M] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ M} {V : Submodule ℂ M} {lam : Fin n → ℝ}

theorem position_perp (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} (i : Fin k) {P : Big n k M} (hP : P ∈ ncV ε V k)
    (hperp : ∀ F ∈ ncV ε V k, (∀ κ, slice i κ F ∈ Wm ε E V) → inner ℂ F P = 0) :
    ∀ κ, slice i κ P ∈ Wp ε E V := by
  classical
  intro κ
  rw [slice_eq_slt]
  generalize (slRest i κ).2 = r
  have hx : slt i r P ∈ ncV ε V 1 := slt_mem_ncV i r hP
  by_cases hr : ∀ j : {j // j ≠ i}, ε (r j).1 ≠ ε (r j).2
  · obtain ⟨xm, hxm, xp, hxp, hdec⟩ := ncV_one_decomp hE hU hV hmono hh hbig hx
    let F : Big n k M :=
      WithLp.toLp 2 (fun κ' => if (slRest i κ').2 = r then xm (fun _ => κ' i) else 0)
    have hFapp : ∀ κ', F κ' = if (slRest i κ').2 = r then xm (fun _ => κ' i) else 0 :=
      fun κ' => rfl
    have hsltF : ∀ r', slt i r' F = if r' = r then xm else 0 := by
      intro r'
      apply PiLp.ext
      intro ι
      have e1 : slt i r' F ι = F ((slRest i).symm (ι 0, r')) := rfl
      rw [e1, hFapp]
      simp only [Equiv.apply_symm_apply, slRest_symm_self]
      by_cases hr' : r' = r
      · rw [if_pos hr', if_pos hr']
        rw [show (fun _ : Fin 1 => ι 0) = ι from funext fun z => by rw [Subsingleton.elim z 0]]
      · rw [if_neg hr', if_neg hr']
        rfl
    have hFm : F ∈ ncV ε V k := by
      rw [slt_mem_ncV_iff]
      intro κ'
      rw [hFapp]
      by_cases h1 : (slRest i κ').2 = r
      · rw [if_pos h1]
        have hxm1 := Wm_le_ncV hxm
        rw [slt_mem_ncV_iff] at hxm1
        have hv := hxm1 (fun _ => κ' i)
        by_cases h2 : ∀ j, ε (κ' j).1 ≠ ε (κ' j).2
        · rw [if_pos h2]
          rwa [if_pos (fun _ => h2 i)] at hv
        · rw [if_neg h2]
          push_neg at h2
          obtain ⟨j, hj⟩ := h2
          by_cases hji : j = i
          · subst hji
            rwa [if_neg (fun hall => (hall 0) hj)] at hv
          · exfalso
            have hκj : κ' j = r ⟨j, hji⟩ := by
              rw [← h1]
              rfl
            exact hr ⟨j, hji⟩ (by rw [← hκj]; exact hj)
      · rw [if_neg h1]
        exact Submodule.zero_mem _
    have hslF : ∀ κ', slice i κ' F ∈ Wm ε E V := by
      intro κ'
      rw [slice_eq_slt, hsltF]
      split_ifs
      · exact hxm
      · exact Submodule.zero_mem _
    have h0 := hperp F hFm hslF
    rw [slt_inner_eq_sum i F P, Finset.sum_eq_single r
      (fun r' _ hr' => by rw [hsltF, if_neg hr', inner_zero_left])
      (fun h => absurd (Finset.mem_univ r) h), hsltF, if_pos rfl, hdec, inner_add_right,
      Wm_perp_Wp hU hxm hxp, add_zero] at h0
    have hxm0 : xm = 0 := inner_self_eq_zero.mp h0
    rw [hdec, hxm0, zero_add]
    exact hxp
  · push_neg at hr
    obtain ⟨j, hj⟩ := hr
    have hz : slt i r P = 0 := by
      apply PiLp.ext
      intro ι
      have e1 : slt i r P ι = P ((slRest i).symm (ι 0, r)) := rfl
      rw [e1]
      have hP' := (slt_mem_ncV_iff.mp hP) ((slRest i).symm (ι 0, r))
      rw [if_neg] at hP'
      · simpa using hP'
      · intro hall
        exact hall j.1 (by rw [slRest_symm_ne i _ r j.2]; exact hj)
    rw [hz]
    exact Submodule.zero_mem _

theorem crossOp_position_bound (hE : IsGlRep E) (hU : IsInfUnitary ε E) (hV : IsKIrrHW ε E (lowK ε lam) V)
    (hmono : StrictAnti lam) {h : ℝ} (hh : GapAtLeast ε lam h)
    (hbig : 2 * (n : ℝ) < h) {k : ℕ} (i : Fin k) {P : Big n k M} (hP : ∀ κ, slice i κ P ∈ Wp ε E V) :
    2 * (h - n + 1) * ‖P‖ ^ 2 ≤ 2 * RCLike.re (inner ℂ (crossOp ε E k i P) P) := by
  classical
  have hslt : ∀ r, slt i r P ∈ Wp ε E V := by
    intro r
    rcases isEmpty_or_nonempty (Fin n × Fin n) with he | ⟨⟨p⟩⟩
    · rw [slt_big_one_eq_zero he (slt i r P)]
      exact Submodule.zero_mem _
    · rw [slt_eq_slice i r p P]
      exact hP _
  have h1 : ‖P‖ ^ 2 = ∑ r, ‖slt i r P‖ ^ 2 := by
    rw [@norm_sq_eq_re_inner ℂ, slt_inner_eq_sum i P P, map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [@norm_sq_eq_re_inner ℂ]
  have h2 : inner ℂ (crossOp ε E k i P) P =
      ∑ r, inner ℂ (crossOp ε E 1 0 (slt i r P)) (slt i r P) := by
    rw [slt_inner_eq_sum i]
    simp only [slt_crossOp]
  rw [h1, h2, map_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_le_sum fun r _ => Wp_bound hE hU hV hmono hh hbig (hslt r)

end Slot

end ReciprocityTheory.ChartRestriction.DS.G2
