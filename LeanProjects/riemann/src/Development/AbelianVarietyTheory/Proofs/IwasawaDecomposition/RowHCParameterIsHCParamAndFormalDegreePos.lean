import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CdScaleTieIff

open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.Mem.Vol
open scoped TensorProduct

namespace GlobalTheory.Mem.Vol

theorem lamS_succ_lt (R : Ranks) (P : HCParam R) (i j : Fin R.r) (hij : j.val = i.val + 1) :
    lamS R P j < lamS R P i := by
  have hk : R.m + 3 ≤ R.k := R.m_add_three_le_k
  have hm : 2 ≤ R.m := R.two_le_m
  have hjr : j.val < R.k + R.m - 1 := j.isLt
  have hu : ∀ a b : Fin R.k, a.val = b.val → P.u a = P.u b := fun a b h => by rw [Fin.ext h]
  have hb : ∀ a b : Fin R.m, a.val = b.val → P.b a = P.b b := fun a b h => by rw [Fin.ext h]
  unfold Formalism.MainNotions.S.lamS
  by_cases hj : j.val < R.k - 1
  · have hi : i.val < R.k - 1 := by omega
    rw [dif_pos hj, dif_pos hi]
    have key : P.v ⟨j.val, hj⟩ < P.v ⟨i.val, hi⟩ :=
      calc P.v ⟨j.val, hj⟩ < P.u ⟨j.val, by omega⟩ := P.u_gt_v ⟨j.val, hj⟩
        _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp [hij])
        _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
    exact_mod_cast key
  · by_cases hi : i.val < R.k - 1
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      rw [dif_neg hj, dif_pos hj0, dif_pos hi]
      have key : -P.b ⟨j.val - (R.k - 1), hj0⟩ < P.v ⟨i.val, hi⟩ :=
        calc -P.b ⟨j.val - (R.k - 1), hj0⟩ = -P.b ⟨0, by omega⟩ :=
            congrArg (fun x => -x) (hb _ _ (show j.val - (R.k - 1) = 0 by omega))
          _ < P.u ⟨R.k - 1, by omega⟩ := P.u_last_gt (by omega) (by omega)
          _ = P.u ⟨i.val + 1, by omega⟩ := hu _ _ (by simp; omega)
          _ < P.v ⟨i.val, hi⟩ := P.v_gt_u ⟨i.val, hi⟩
      have := (Rat.cast_lt (K := ℝ)).mpr key
      push_cast at this
      exact this
    · have hj0 : j.val - (R.k - 1) < R.m := by omega
      have hi0 : i.val - (R.k - 1) < R.m := by omega
      have hi1 : i.val - (R.k - 1) + 1 < R.m := by omega
      rw [dif_neg hj, dif_pos hj0, dif_neg hi, dif_pos hi0]
      have h1 := P.gap_be ⟨i.val - (R.k - 1), hi0⟩
      have h2 := P.gap_eb ⟨i.val - (R.k - 1), hi0⟩ hi1
      have h3 : P.b ⟨i.val - (R.k - 1) + 1, hi1⟩ = P.b ⟨j.val - (R.k - 1), hj0⟩ := hb _ _ (by simp; omega)
      have ht : (0 : ℚ) ≤ R.t := Nat.cast_nonneg _
      have key : P.b ⟨i.val - (R.k - 1), hi0⟩ < P.b ⟨j.val - (R.k - 1), hj0⟩ := by
        rw [← h3]; linarith
      have := (Rat.cast_lt (K := ℝ)).mpr key
      linarith

theorem lamS_int (R : Ranks) (P : HCParam R) (i : Fin R.r) : ∃ z : ℤ, lamS R P i = (z : ℝ) := by
  unfold Formalism.MainNotions.S.lamS
  split_ifs with h h'
  · obtain ⟨z, hz⟩ := P.v_int ⟨i.val, h⟩
    exact ⟨z, by rw [hz, Rat.cast_intCast]⟩
  · obtain ⟨z, hz⟩ := P.b_int ⟨i.val - (R.k - 1), h'⟩
    exact ⟨-z, by rw [hz, Rat.cast_intCast]; push_cast; ring⟩
  · exact ⟨0, by simp⟩

theorem lamSH_isHCParam (R : Ranks) (P : HCParam R) : Formalism.QuantumDeterminants.IsHCParam (lamSH R P) := by
  refine ⟨?_, ?_⟩
  · rw [Fin.strictAnti_iff_succ_lt]
    intro i
    exact lamS_succ_lt R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) (Fin.castSucc i))
      (Fin.cast (Formalism.MainNotions.S.dimS_eq R) i.succ) (by simp)
  · intro a
    obtain ⟨z, hz⟩ := lamS_int R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a)
    obtain ⟨w, hw⟩ := R.k_even
    have hk : (R.k : ℝ) = 2 * w := by rw [hw]; push_cast; ring
    refine ⟨z - R.rS - w, ?_⟩
    show lamS R P (Fin.cast (Formalism.MainNotions.S.dimS_eq R) a) - _ = _
    rw [hz]
    push_cast
    rw [hk]
    ring

theorem fdegHC_pos_of_injective {n : ℕ} (lam : Fin n → ℝ) (hlam : Function.Injective lam) :
    0 < Formalism.QuantumDeterminants.fdegHC lam := by
  unfold Formalism.QuantumDeterminants.fdegHC
  apply div_pos
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    exact abs_pos.mpr (sub_ne_zero.mpr fun h => hb.2.ne (hlam h))
  · apply Finset.prod_pos
    intro a _
    apply Finset.prod_pos
    intro b hb
    rw [Finset.mem_filter] at hb
    have h1 : (a : ℕ) < b := hb.2
    have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast h1
    linarith

theorem lamSH_isHCParam_and_trueDsig_pos :
    ∀ (R : Ranks) (P : HCParam R), Formalism.QuantumDeterminants.IsHCParam (lamSH R P) ∧ 0 < trueDsig R P := by
  intro R P
  refine ⟨lamSH_isHCParam R P, ?_⟩
  exact fdegHC_pos_of_injective _ (lamSH_isHCParam R P).1.injective

end GlobalTheory.Mem.Vol
