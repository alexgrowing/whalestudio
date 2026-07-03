import Mathlib

-- set_option trace.Meta.synthInstance true -- debug

/-!
使用theorem关键词定义一个定理，分别传入【定理名称】【定理结论】【定理证明】
theorem [name]
: [content]
:= [proof]

往往证明内容暂时写不出来，可以用sorry或by admit省略
-/
section intro1

theorem commutative_in_natural_number
: ∀x : ℕ, x + 1 = 1 + x
:= by admit

theorem commutative_in_natural_number2
: ∀ x : ℕ, x + 1 = 1 + x
:= sorry

theorem commutative_in_natural_number3 (x : ℕ)
: x + 1 = 1 + x
:= by omega

theorem commutative_in_natural_number4 {x : ℕ}
: x + 1 = 1 + x := by
  rw[Nat.add_comm]

theorem commutative_in_natural_number5
: x + 1 = 1 + x -- 由编译器推测x : ℕ
:= by
  simp[Nat.add_comm]

theorem commutative_in_natural_number6 {x}
: x + 1 = 1 + x := by
  omega

theorem commutative_in_natural_number7 (x)
: x + 1 = 1 + x := by
  omega

example
: ∀ x : ℕ, x + 1 = 1 + x := by
  omega

example (x : ℕ)
: x + 1 = 1 + x := by
  omega

example
: x + 1 = 1 + x := by
  omega

example {x}
: x + 1 = 1 + x := by
  simp[Nat.add_comm]

example (x)
: x + 1 = 1 + x := by
  omega

end intro1

/-!
三种证明方法：正向证明、等价结论、反证法，先介绍正向证明
-/
section intro2


end intro2
