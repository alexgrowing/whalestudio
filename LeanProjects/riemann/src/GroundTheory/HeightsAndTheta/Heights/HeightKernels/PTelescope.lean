import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.RationalSections.ThmISt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

namespace TelescopingSum

theorem comp_swap {α : Type*} (D k : ℕ) (hk : k < D + 1) (X Y : α) (m : ℕ) (hm : m = k ∨ m = k + 1) :
    (fun j : Fin (D + 1) => if (j : ℕ) < m then X else Y) ∘ Equiv.swap ⟨k, hk⟩ (Fin.last D) =
      Fin.snoc (fun j : Fin D => if (j : ℕ) < k then X else Y) (if k < m then X else Y) := by
  funext j
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [Equiv.swap_apply_right]
  · simp only [Function.comp_apply, Fin.snoc_castSucc]
    by_cases h : (j' : ℕ) = k
    · have hj : Fin.castSucc j' = ⟨k, hk⟩ := Fin.ext (by simp [h])
      rw [hj, Equiv.swap_apply_left]
      have := j'.isLt
      simp only [Fin.val_last]
      rw [if_neg (by omega), if_neg (by omega)]
    · have h1 : Fin.castSucc j' ≠ ⟨k, hk⟩ := fun e => h (by simpa using congrArg Fin.val e)
      have h2 : Fin.castSucc j' ≠ Fin.last D := Fin.castSucc_ne_last j'
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      simp only [Fin.val_castSucc]
      rcases hm with rfl | rfl
      · rfl
      · by_cases h3 : (j' : ℕ) < k
        · rw [if_pos h3, if_pos (by omega)]
        · rw [if_neg h3, if_neg (by omega)]

end TelescopingSum

theorem Telescope.proof : TelescopeStatement := by
  intro K _ ι _ I hI P D A u hu hP hA hus
  set W := HermLine.ofWeight u hu with hWdef
  have hW : IsSmoothHerm W := by
    have : W.h = fun z => Real.exp (-u z) := rfl
    unfold IsSmoothHerm
    rw [this]
    exact Real.contDiff_exp.comp_contDiffOn hus.neg
  have hA' : IsSmoothHerm (A.tensor W) := by
    unfold IsSmoothHerm at hA hW ⊢
    exact hA.mul hW
  obtain ⟨T, hT⟩ : ∃ T : ℕ → ℝ, ∀ m, T m =
      I P (D + 1) (fun j : Fin (D + 1) => if (j : ℕ) < m then A.tensor W else A) := ⟨_, fun _ => rfl⟩
  have hsm : ∀ (m : ℕ) (j : Fin (D + 1)), IsSmoothHerm (if (j : ℕ) < m then A.tensor W else A) :=
    fun m j => by split_ifs <;> assumption
  have hstep : ∀ k ∈ Finset.range (D + 1), T (k + 1) - T k =
      -ptsIntegral P (pot fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) u := by
    intro k hk
    have hk' : k < D + 1 := Finset.mem_range.mp hk
    have hL : ∀ j : Fin D, IsSmoothHerm (if (j : ℕ) < k then A.tensor W else A) :=
      fun j => by split_ifs <;> assumption
    have e1 : T (k + 1) = I P (D + 1)
        (Fin.snoc (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) (A.tensor W)) := by
      rw [hT, ← hI.1 P (D + 1) _ (Equiv.swap ⟨k, hk'⟩ (Fin.last D)) hP (hsm (k + 1)),
        TelescopingSum.comp_swap D k hk' _ _ (k + 1) (Or.inr rfl), if_pos (Nat.lt_succ_self k)]
    have e0 : T k = I P (D + 1)
        (Fin.snoc (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A) A) := by
      rw [hT, ← hI.1 P (D + 1) _ (Equiv.swap ⟨k, hk'⟩ (Fin.last D)) hP (hsm k),
        TelescopingSum.comp_swap D k hk' _ _ k (Or.inl rfl), if_neg (lt_irrefl k)]
    have hmc := metricChange K ι I hI P D (fun j : Fin D => if (j : ℕ) < k then A.tensor W else A)
      A u hu hP hL hA hus
    rw [e1, e0, hmc]
    ring
  have h0 : T 0 = I P (D + 1) (fun _ => A) := by
    rw [hT]
    simp
  have hD : T (D + 1) = I P (D + 1) (fun _ => A.tensor W) := by
    rw [hT]
    congr 1
    funext j
    rw [if_pos j.isLt]
  rw [← h0, ← hD, ← Finset.sum_range_sub, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl hstep

end GroundTheory.Heights₂.Heights
