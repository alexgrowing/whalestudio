import Mathlib

namespace UnitBallK

variable (K : Type*) [NormedField K] [IsUltrametricDist K]

def subring : Subring K where
  carrier := {x | ‖x‖ ≤ 1}
  zero_mem' := by simp
  one_mem' := by simp
  neg_mem' := by
    intro x hx
    simpa using hx
  add_mem' := by
    intro x y hx hy
    have key : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y
    rcases le_max_iff.1 key with h | h
    · exact le_trans h hx
    · exact le_trans h hy
  mul_mem' := by
    intro x y hx hy
    have hx' : ‖x‖ ≤ 1 := hx
    have hy' : ‖y‖ ≤ 1 := hy
    have h0x := norm_nonneg x
    have h0y := norm_nonneg y
    change ‖x * y‖ ≤ 1
    rw [norm_mul]
    nlinarith

variable {K}

theorem add_mem {x y : K} (hx : x ∈ subring K) (hy : y ∈ subring K) : x + y ∈ subring K :=
  (subring K).add_mem hx hy

theorem mul_mem {x y : K} (hx : x ∈ subring K) (hy : y ∈ subring K) : x * y ∈ subring K :=
  (subring K).mul_mem hx hy

end UnitBallK
