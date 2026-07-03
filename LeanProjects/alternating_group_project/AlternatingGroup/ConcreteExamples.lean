/-
  AlternatingGroup/ConcreteExamples.lean

  具体验证：A₃ 和 A₄ 的情形。

  - A₃ = {e, (0 1 2), (0 2 1)} 仅有3个元素，全由3-轮换生成。
  - A₄ 有 12 个元素，由 8 个 3-轮换生成（每个3-轮换有 2 个写法，共4个轨道×2=8个）。
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Cycle.Concrete
import Mathlib.GroupTheory.AlternatingGroup
import AlternatingGroup.ElementaryProof

open Equiv Perm ElementaryProof

/-! ## A₃ 的具体验证 -/

section A3

/-- Fin 3 上唯一的非平凡3-轮换：(0 1 2) = (swap 0 1)(swap 1 2) -/
def cyc3 : Perm (Fin 3) := swap 0 1 * swap 1 2

/-- cyc3 的显式值 -/
lemma cyc3_apply_zero : cyc3 0 = 1 := by native_decide
lemma cyc3_apply_one  : cyc3 1 = 2 := by native_decide
lemma cyc3_apply_two  : cyc3 2 = 0 := by native_decide

/-- cyc3 是偶置换 -/
lemma cyc3_sign : cyc3.sign = 1 := by native_decide

/-- cyc3 ∈ A₃ -/
lemma cyc3_mem_A3 : cyc3 ∈ alternatingGroup (Fin 3) := by
  rw [mem_alternatingGroup]; exact cyc3_sign

/-- A₃ 由 3-轮换生成（n=3 情形） -/
theorem A3_generated_by_3cycles :
    alternatingGroup (Fin 3) = Subgroup.closure (S3 3) :=
  alternatingGroup_eq_closure_s3 3 le_rfl

end A3

/-! ## A₄ 的具体验证 -/

section A4

/-- A₄ 中所有 3-轮换之一：(0 1 2) -/
def c012 : Perm (Fin 4) := swap 0 1 * swap 1 2

/-- A₄ 中所有 3-轮换之一：(0 1 3) -/
def c013 : Perm (Fin 4) := swap 0 1 * swap 1 3

/-- 验证 c012 是偶置换 -/
lemma c012_sign : c012.sign = 1 := by native_decide

/-- 验证 c013 是偶置换 -/
lemma c013_sign : c013.sign = 1 := by native_decide

/-- A₄ 由 3-轮换生成（n=4 情形） -/
theorem A4_generated_by_3cycles :
    alternatingGroup (Fin 4) = Subgroup.closure (S3 4) :=
  alternatingGroup_eq_closure_s3 4 (by norm_num)

end A4

/-! ## 一般 n 的显式推论 -/

/-- 对任意 n ≥ 3，closure(S3 n) = Aₙ -/
theorem general_closure_eq (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.closure (S3 n) = alternatingGroup (Fin n) :=
  (alternatingGroup_eq_closure_s3 n hn).symm

/-- Aₙ 中每个元素都是 3-轮换的乘积（n ≥ 3） -/
theorem every_even_perm_is_product_of_3cycles
    (n : ℕ) (hn : 3 ≤ n) (σ : Perm (Fin n))
    (hσ : σ ∈ alternatingGroup (Fin n)) :
    σ ∈ Subgroup.closure (S3 n) := by
  rw [general_closure_eq n hn]
  exact hσ
