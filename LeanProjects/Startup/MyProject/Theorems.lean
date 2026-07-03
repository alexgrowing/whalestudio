-- MyProject/Theorems.lean
-- 定理与证明

import MyProject.Basic

namespace MyProject

/-- 定理：double n = n + n -/
theorem double_eq_add (n : Nat) : double n = n + n := by
  simp [double]; omega

/-- 定理：0 是偶数 -/
theorem zero_isEven : isEven 0 = true := by
  decide

/-- 定理：偶数加 2 仍是偶数 -/
theorem even_add_two (n : Nat) (h : isEven n = true) : isEven (n + 2) = true := by
  simp [isEven] at *; omega

/-- 定理：double 是单调的（n ≤ m → double n ≤ double m） -/
theorem double_mono {n m : Nat} (h : n ≤ m) : double n ≤ double m := by
  simp [double]; omega

/-- 定理：factorial 总是正数 -/
theorem factorial_pos (n : Nat) : 0 < factorial n := by
  induction n with
  | zero      => simp [factorial]
  | succ n ih =>
    simp only [factorial]
    exact Nat.mul_pos (Nat.succ_pos n) ih

/-- 定理：myMax 满足交换律 -/
theorem myMax_comm (a b : Nat) : myMax a b = myMax b a := by
  simp [myMax, Nat.max_comm]

end MyProject
