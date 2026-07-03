-- MyProject/Basic.lean
-- 核心函数定义

namespace MyProject

/-- 将自然数翻倍 -/
def double (n : Nat) : Nat := n * 2

/-- 计算阶乘 -/
def factorial : Nat → Nat
  | 0     => 1
  | n + 1 => (n + 1) * factorial n

/-- 计算斐波那契数列第 n 项 -/
def fibonacci : Nat → Nat
  | 0     => 0
  | 1     => 1
  | n + 2 => fibonacci n + fibonacci (n + 1)

/-- 判断自然数是否为偶数 -/
def isEven (n : Nat) : Bool := n % 2 == 0

/-- 两个自然数取最大值（直接用 Nat.max） -/
def myMax (a b : Nat) : Nat := Nat.max a b

end MyProject

export MyProject (double factorial fibonacci isEven myMax)
