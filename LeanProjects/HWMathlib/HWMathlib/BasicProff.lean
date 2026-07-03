import Mathlib.Tactic.ByContra
import Mathlib.Tactic


set_option linter.style.longLine false
set_option linter.style.whitespace false

section ProofTest1 -- 证明1 + 1 = 2
def addProof : Nat → Nat → Nat
  | Nat.zero, n => n
  | Nat.succ m, n => Nat.succ (addProof m n)

theorem one_plus_one_eq_two : addProof (Nat.succ Nat.zero) (Nat.succ Nat.zero) = Nat.succ (Nat.succ Nat.zero):=
rfl
end ProofTest1

section ProofTest2
variable (x y : Nat)

def double := x + x
#check double y
#check double (2 * x)

attribute [local simp] Nat.add_assoc Nat.add_comm Nat.add_left_comm

-- 证明 2 * (x + y) = 2 * x + 2 * y
theorem t1 : double (x + y) = double x + double y := by
  simp [double]

-- 证明 2 * (x * y) = 2 * x * y
theorem t2 : double (x * y) = double x * y := by
  simp [double, Nat.add_mul]


end ProofTest2

-- 离散数学的证明
section ProofTest3

theorem proof1 {A B : Prop} : A → (B → A) := by
  intro a _
  exact a

theorem proof2 {A B C : Prop} : (A → (B → C)) → (A → B) → (A → C) := by
  intro h₁ h₂ h₃
  exact (h₁ h₃) (h₂ h₃)

theorem proof3 {A B : Prop} : (¬B → ¬A) → (¬B → A) → B := by
  intro h₁ h₂
  by_contra h₃
  have h₄ := h₁ h₃
  have h₅ := h₂ h₃
  contradiction

example (h₁ : a → b) (h₂ : a) : b := by
  apply h₁
  exact h₂

example (h₁ : a → b) (h₂ : b → c) : a → c := by
  intro x
  apply h₂
  apply h₁
  exact x

theorem xyz1 {a b c : Prop} (h₁ : a → b) (h₂ : b → c) : a → c := by
  intro x
  apply h₂
  apply h₁
  exact x

theorem xyz2 {a b c : Prop} : (a → b) → (b → c) → a → c := by
  intro h₁ h₂ h₃
  apply h₂
  apply h₁
  exact h₃

end ProofTest3

section ProofTest4

inductive WuXing : Type
  | metal -- 金
  | wood  -- 木
  | water -- 水
  | fire  -- 火
  | earth -- 土
open WuXing

-- 定义相生关系
def generates : WuXing → WuXing → Bool
  | water, wood => true
  | wood, fire => true
  | fire, earth => true
  | earth, metal => true
  | metal ,water => true
  | _, _ => false

-- 定义相克关系
def overcomes : WuXing → WuXing → Bool
  | water, fire => true
  | fire, metal => true
  | metal, wood => true
  | wood, earth => true
  | earth, water => true
  | _, _ => false

example : generates water wood := by simp [generates]
example : overcomes water fire := by simp [overcomes]
example : ¬generates water fire := by simp [generates]
example : ¬overcomes water wood := by simp [overcomes]

end ProofTest4

-- 如果a>0且b>0，则a+b>0
section ProofTest5

example  (a b : ℝ) (ha : a > 0) (hb : b > 0) : a + b > 0 := by linarith

end ProofTest5

-- 两个偶数之和是偶数
section ProofTest6
example (a b : ℤ) (ha : Even a) (hb : Even b) : Even (a + b) := by
  obtain⟨m, hm⟩  := ha -- 拆开ha:存在m使得a=m+m,因为Even a本质是一个存在命题∃r, a = r + r,这里的obtain就是把r和a=r+r取出来分别命题为m和hm
  obtain⟨n, hn⟩ := hb  -- 拆开hb:存在n使得b=n+n
  use m + n            -- 证明存在命题时,提供具体的存在对象
  linarith             -- 让linarith自动验证代数等式a+b=(m+n)+(m+n)


end ProofTest6
