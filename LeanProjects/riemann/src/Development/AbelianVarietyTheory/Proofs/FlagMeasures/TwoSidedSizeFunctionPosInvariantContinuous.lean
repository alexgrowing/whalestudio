import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsNormalFormStabilizerMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ContinuousOnMajorantFlagLengths

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.TwoSided

open GlobalTheory.Mom.LowVec

theorem exists_coord {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (a : Fin (r + 1)) :
    ∃ i : Fin (2 * r + k + 1), a.val ≤ i.val ∧ fvec k r z a i ≠ 0 := by
  by_cases ha : a.val < r
  · refine ⟨eI k r ⟨a.val, ha⟩, le_of_eq rfl, ?_⟩
    simp only [fvec, dif_pos ha, bvec, Pi.single_eq_same]
    exact one_ne_zero
  ·
    have hz0 : ∃ i, z i ≠ 0 := by
      by_contra h
      push_neg at h
      have : z = 0 := funext h
      subst this
      simp [Tz, herm] at hT
    obtain ⟨i, hi⟩ := hz0
    have hri : r ≤ i.val := by
      by_contra h
      exact hi (hz i (Or.inl (Nat.lt_of_not_le h)))
    refine ⟨i, le_trans (Nat.le_of_lt_succ a.isLt) hri, ?_⟩
    simp only [fvec, dif_neg ha]
    exact hi

theorem lA_pos {k r : ℕ} {z : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z)
    {x : Mat k r} (hx : x ∈ GG k r) (a : Fin (r + 1)) : 0 < lA k r z x a := by
  obtain ⟨i, hai, hi⟩ := exists_coord hz hT a
  have hu : IsUnit x.det := Formalism.QuantumDeterminants.WeylGroupFacts.isUnit_of_uh hx
  have hc : 0 < ∑ j, ‖x i j‖ + 1 := by positivity

  have key : ∀ y ∈ Submodule.span ℂ (Set.range fun b : {b : Fin r // b.val < a.val} =>
      Formalism.QuantumDeterminants.bvec (Formalism.QuantumDeterminants.eI k r b.1)),
      ‖fvec k r z a i‖ / (∑ j, ‖x i j‖ + 1) ≤ eucl (x⁻¹ *ᵥ (fvec k r z a - y)) := by
    intro y hy
    have hy' : y ∈ GlobalTheory.Mom.LowVec.flagSpan k r a := hy
    have hyi : y i = 0 := (GlobalTheory.Mom.LowVec.mem_flagSpan.1 hy') i hai
    set w := x⁻¹ *ᵥ (fvec k r z a - y) with hw
    have hv : fvec k r z a - y = x *ᵥ w := by
      rw [hw, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv x hu, Matrix.one_mulVec]
    have hvi : fvec k r z a i = ∑ j, x i j * w j := by
      have := congrFun hv i
      simp only [Pi.sub_apply, hyi, sub_zero] at this
      rw [this]
      rfl
    have hwe : 0 ≤ eucl w := Real.sqrt_nonneg _
    have hle : ‖fvec k r z a i‖ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by
      rw [hvi]
      calc ‖∑ j, x i j * w j‖ ≤ ∑ j, ‖x i j * w j‖ := norm_sum_le _ _
        _ = ∑ j, ‖x i j‖ * ‖w j‖ := by simp only [norm_mul]
        _ ≤ ∑ j, ‖x i j‖ * eucl w := by
          gcongr with j
          exact GlobalTheory.Amp.LInv.norm_le_eucl w j
        _ = (∑ j, ‖x i j‖) * eucl w := by rw [Finset.sum_mul]
        _ ≤ (∑ j, ‖x i j‖ + 1) * eucl w := by nlinarith
    rw [div_le_iff₀ hc]
    linarith
  unfold lA
  refine lt_of_lt_of_le (div_pos (norm_pos_iff.mpr hi) hc) ?_
  refine le_csInf ⟨_, 0, Submodule.zero_mem _, rfl⟩ ?_
  rintro t ⟨y, hy, rfl⟩
  exact key y hy

theorem Sg2_invariant_continuousOn_one_le_bounds : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → 0 < Tz k r z → (∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a) ∧ (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), Sg2 k r z (s * x * κ) = Sg2 k r z x) ∧ ContinuousOn (Sg2 k r z) (GG k r) ∧ ∀ x, 1 ≤ Sg2 k r z x ∧ Sg k r z x ≤ Sg2 k r z x ∧ (∀ a, lA k r z x a ≤ Sg2 k r z x ∧ (lA k r z x a)⁻¹ ≤ Sg2 k r z x) ∧ (Sg2 k r z x = 1 ∨ ∃ a, Sg2 k r z x = max (lA k r z x a) (lA k r z x a)⁻¹) := by
  intro k r z hz hT
  have hpos : ∀ x ∈ GG k r, ∀ a, 0 < lA k r z x a := fun x hx a => lA_pos hz hT hx a
  obtain ⟨hinv, -, hSg⟩ := GlobalTheory.Amp.LInv.lengths_basic k r z hz
  refine ⟨hpos, ?_, ?_, ?_⟩
  · intro x hx s hs κ hκ
    have h := (hinv x hx s hs κ hκ).1
    simp only [Sg2, h]
  · have hc := (GlobalTheory.Amp.LenCont.lA_Sg_continuousOn k r z).1
    exact GlobalTheory.Amp.LenCont.fold_continuousOn (GG k r) (fun a x => max (lA k r z x a) (lA k r z x a)⁻¹)
      (fun a => continuous_max.comp_continuousOn (ContinuousOn.prodMk (hc a) (ContinuousOn.inv₀ (hc a) fun x hx => (hpos x hx a).ne'))) Finset.univ
  · intro x
    have hle : ∀ a, max (lA k r z x a) (lA k r z x a)⁻¹ ≤ Sg2 k r z x := fun a =>
      (Finset.le_fold_max _).2 (Or.inr ⟨a, Finset.mem_univ _, le_rfl⟩)
    have h1 : 1 ≤ Sg2 k r z x := (Finset.le_fold_max _).2 (Or.inl le_rfl)
    refine ⟨h1, ?_, fun a => ⟨(le_max_left _ _).trans (hle a), (le_max_right _ _).trans (hle a)⟩, ?_⟩
    · exact (Finset.fold_max_le _).2 ⟨h1, fun a _ => (le_max_left _ _).trans (hle a)⟩
    ·
      have key : ∀ s : Finset (Fin (r + 1)), s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = 1 ∨
          ∃ a, s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹) = max (lA k r z x a) (lA k r z x a)⁻¹ := by
        intro s
        refine Finset.induction_on s ?_ ?_
        · left
          simp
        · intro a s ha ih
          rw [Finset.fold_insert ha]
          rcases max_choice (max (lA k r z x a) (lA k r z x a)⁻¹)
              (s.fold max 1 (fun a => max (lA k r z x a) (lA k r z x a)⁻¹)) with h | h
          · exact Or.inr ⟨a, h⟩
          · rw [h]
            exact ih
      exact key Finset.univ

end GlobalTheory.Amp.TwoSided
