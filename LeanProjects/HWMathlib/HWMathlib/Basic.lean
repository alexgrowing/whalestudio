/-
Copyright (c) 2026 Little Sail. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Little Sail
-/

import Mathlib.Data.Real.Basic
import Mathlib

set_option linter.style.header false
set_option linter.style.whitespace false
set_option linter.style.longLine false
set_option linter.style.emptyLine false

example (a b : ℝ) : a * b = b * a := by
  rw [mul_comm a b]


def twice_double (x : ℕ) : Nat :=
  let y := x * 2;let z := y * y;
  z * 8

#eval twice_double 3

#eval (1-2:Nat)
#eval (1-2:ℤ)
#eval (1-2:Int)

def b:Bool := true
def doNothing:Unit := ()
#check doNothing

def xyz:Float := 3/4
#eval xyz

def sample2Parameter (ak : Int) := ak * ak
#eval sample2Parameter 20

def square : Nat → Nat :=
  fun n => n * n

#eval square 5

def sum : Nat → Nat → Nat :=
  fun a b => a + b

#eval sum 3 4

def double2 : Nat → Nat :=
  fun x => x * 2

def compose2 : (Nat → Nat) → (Nat → Nat) → Nat → Nat :=
  fun f g n => f (g n)

def compose : (Nat → Nat) → (Nat → Nat) → Nat → Nat :=
  fun f g n => f (g n)

def compose3 (f : Nat → Nat) (g : Nat → Nat) (n : Nat) : Nat :=
  f (g n)

#check Type
#check Nat
#check Type 0

section
  variable (a b : Nat) (b : Float) (f : Nat → Nat)
  def doTwice := f (f a)
  def fn (n : Nat) := n ^ 2

  def anotherNumber := doTwice 3 fn
  #eval anotherNumber
end

#eval (· - 1) 5

def div (a b : Float) := a / b
def div2 (a : Float) := div a 2
#eval div2 8

def factorial1 (n : Nat) :=
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial1 n

def factorial2 : Nat → Nat :=
  fun n =>
  match n with
  | 0 => 1
  | n + 1 => (n + 1) * factorial2 n

def factorial3 : Nat → Nat
  | 0 => 1
  | n + 1 => (n + 1) * factorial3 n

#eval ¬ true
#eval true → false
#eval true ↔ false
#eval true ∧ false
#eval true ∨ false

#check List.nil
#check List.cons
#check List.map

def test (n : Nat) : IO Unit := do
  let numbers : List Nat := [1, 2, 3, 4, 5]
  for i in numbers do
    IO.println (i + n)
  IO.println "Done!"

#eval test 5

def main : IO Unit := do
  let names := ["Alice", "Bob", "Charlie"]
  for name in names do
    IO.println s!"Hello, {name}!"
  IO.println "All greetings have been printed."


inductive MyNat2 where
  | zero
  | suc : MyNat2 → MyNat2
  | suc2 (n : MyNat2) : MyNat2


#eval MyNat2.suc (MyNat2.suc MyNat2.zero)

def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops k)

#eval evenLoops 6

inductive MyTree (α : Type) where
  | leaf
/--
node本质上是一个连续接受三个参数的函数（这个函数的返回值是Tree α，但这个函数是没有函数体的）
它不是一次接受一个三元组
-/
  | node : MyTree α → MyTree α → α → MyTree α
/--
三元组的方式强调了节点的三个字段是一个整体，不能单独使用，但多了一层tuple的包装
-/
  | node2 : (MyTree α × MyTree α × α) → MyTree α
/--
node3的方式与node的方式类似，但在调用的时候除了
def t : MyTree Nat := MyTree.node3 MyTree.leaf MyTree.leaf 3
还可以
def t : MyTree Nat := MyTree.node3 (t1 := MyTree.leaf) (t2 := MyTree.leaf) (v := 3)
-/
  | node3 (t1 :MyTree α) (t2 : MyTree α) (v : α)

def myTree : MyTree String :=
  MyTree.node (MyTree.node MyTree.leaf MyTree.leaf "A")  (MyTree.node MyTree.leaf  MyTree.leaf "C") "B"

#eval myTree

def size : MyTree α → Nat
  | MyTree.leaf => 0
  | MyTree.node left right _ => size left + size right + 1
  | MyTree.node2 (left, right, _) => size left + size right + 1
  | MyTree.node3 left right _ => size left + size right + 1


-- TODO 1 = Nat.succ Nat.zero，这个等号是怎么建立起来的，去研究一下OfNat类的实现吧
#eval Nat.succ Nat.zero


example : (1 : Nat) = Nat.succ Nat.zero := rfl

structure Point (α : Type) where
  x : α
  y : α

inductive Color where
  | red
  | green
  | blue

structure ColorPoint (α : Type) extends Point α where
  c : Color

def cp : ColorPoint Nat := { x := 1, y := 2, c := Color.red }
def cp2 := { x := 1, y := 2, c := Color.red: ColorPoint _ }

section
/-- 三种方式创建结构体，默认结构体构造子的名字以及重命名 -/
  structure PP where
    make ::
    x : Float
    y : Float

  def cpp1 :=  PP.make 1.0 2.0
  def cpp2 := { x := 1.0, y := 2.0 : PP }
  def cpp3 : PP := { x := 1.0, y := 2.0 }

  structure PP2 where
    x : Float
    y : Float

  def cpp4 :=  PP2.mk 1.0 2.0

  #eval PP2.x cpp4
  #eval cpp4.x
end

section
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | _ => false

def isZero2 : Nat → Bool
  | Nat.zero => true
  | _ => false
end


section

inductive Weekday where
| sunday
| monday
| tuesday
open Weekday -- 加了open，下面就可以直接写monday，不用写Weekday.monday

def numberOfDay : Weekday → Nat
| sunday => 0
| monday => 1
| _ => 100

end

section
def length {α : Type} : List α → Nat
| [] => 0
| _ :: xs => 1+ length xs

/--
只是为了看一下xs是什么，就变得这么复杂
-/
def lengthIO {α : Type} [Repr α ]: List α → IO Nat
| [] => pure 0
| _ :: xs => do
    IO.println s!"xs = {repr xs}"
    let n ← lengthIO xs
    pure (1 + n)

#eval length [4, 5, 6]
#eval lengthIO [1, 2, 3]


end


section poly

def identify (α : Type) (x : α) : α := x

end poly


section classtest

class AddClass (α : Type) where
  add : α → α → α

instance : AddClass Nat where
  add := Nat.add

instance : AddClass Int where
  add := Int.add

instance : AddClass Float where
  add := Float.add

#eval AddClass.add 2 2
#eval AddClass.add (2 : Int) (2 : Int)
#eval AddClass.add 2.0 2.0

end classtest


section implicitArgs

def add {α : Type} [Add α] (a b : α) : α := a + b

end implicitArgs

section ListTest

def length1 (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => 0
  | List.cons _ ys => 1 + length1 α ys

def length2 {α : Type} : List α → Nat
  | [] => 0
  | List.cons _ tail => 1 + length2 tail


def length3 {α : Type} : List α → Nat
  | [] => 0
  | _ :: tail => 1 + length3 tail

end ListTest

section Listmap

def add_one (x : Nat) : Nat := x + 1

def l := [1, 2, 4, 6]
def l2 := l.map add_one
#eval l2

end Listmap

section threeTypeOfReturn

#eval [].headD 5
#eval ([] : List Int).head?
#eval ([] : List Int).head?

end threeTypeOfReturn

section

def simpleJob : IO Unit := do
  let mut i := 100
  while i > 90 do
    IO.println i
    i := i - 1

end

section arraytest

def arraytestIO : IO Unit := do
  let a₁ : Array Nat := #[1, 2, 3, 4, 5]
  IO.println a₁

  let a₂ : Array Int := Array.mk [10, 20, 30]
  IO.println a₂

  IO.println a₁[0]

  let a₃ := Array.qsort a₁ (· > ·)
  IO.println a₃

  let a₄ := Array.qsort a₂ (fun x y => x > y)
  IO.println a₄

#eval arraytestIO

end arraytest

section Typetest

inductive ExamStatus
| attended
| notAttended

def Score(status : ExamStatus) : Type :=
  match status with
  | ExamStatus.attended => Nat
  | ExamStatus.notAttended => String


-- 居然有Σ（Sigma）和∑（sum）的区别
-- Σ称之为依赖和类型，第二项的类型依赖于第一项
def StudentWithScore : Type := Σ(status : ExamStatus), Score status

#print StudentWithScore

def SWS : Type := Sigma fun status : ExamStatus => Score status

#print SWS

def SWS2 : Type := (status : ExamStatus) × Score status

#print SWS2

def student1 : StudentWithScore := ⟨ExamStatus.attended, (10:Nat)⟩
def student2 : SWS := ⟨ExamStatus.attended, (80:Nat)⟩
def student3 : SWS2 := ⟨ExamStatus.notAttended, "缺席"⟩

end Typetest
