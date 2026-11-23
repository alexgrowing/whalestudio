import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.StripEstimates.FaceMapCompSuccAboveCastSucc

open Ad3 Ad3.S

namespace GlobalTheory.CompanionTheory.HalfWeight

theorem GS_eq_sum_zmod (d : ℕ) [NeZero d] (r : ℤ) :
    GS r d = ∑ y : ZMod d, ZMod.stdAddChar ((r : ZMod d) * y ^ 2) := by
  unfold GS
  refine Finset.sum_nbij' (fun x : ℕ => (x : ZMod d)) ZMod.val ?_ ?_ ?_ ?_ ?_
  · intro x _; simp
  · intro y _; simpa using ZMod.val_lt y
  · intro x hx; exact ZMod.val_cast_of_lt (Finset.mem_range.mp hx)
  · intro y _; simp
  · intro x _
    have hc : ((r : ZMod d) * (x : ZMod d) ^ 2) = ((r * (x : ℤ) ^ 2 : ℤ) : ZMod d) := by
      push_cast; ring
    rw [hc, ZMod.stdAddChar_coe]
    unfold ee
    congr 1
    push_cast
    ring

theorem gauss_sum_conjugation : T4 := by
  intro M d a b c' hd h
  have : NeZero d := ⟨hd.ne'⟩
  have h1 : (-(b : ZMod d)) * (4 * (M : ZMod d) ^ 2 * (c' : ZMod d)) = 1 := by
    have h2 := congrArg (Int.cast : ℤ → ZMod d) h
    push_cast at h2
    rw [ZMod.natCast_self] at h2
    linear_combination h2
  let u : (ZMod d)ˣ :=
    ⟨2 * (M : ZMod d) * (c' : ZMod d), -(b : ZMod d) * 2 * (M : ZMod d),
      by linear_combination h1, by linear_combination h1⟩
  rw [GS_eq_sum_zmod, GS_eq_sum_zmod, map_sum,
    ← Equiv.sum_comp (Units.mulLeft u) (fun y : ZMod d =>
      (starRingEnd ℂ) (ZMod.stdAddChar ((b : ZMod d) * y ^ 2)))]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← AddChar.map_neg_eq_conj]
  congr 1
  simp only [Units.mulLeft_apply, u]
  linear_combination ((c' : ZMod d) * y ^ 2) * h1

end GlobalTheory.CompanionTheory.HalfWeight
