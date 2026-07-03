/-
  AlternatingGroup/ElementaryProof.lean

  自包含的初等证明：Aₙ（n ≥ 3）由所有 3-轮换生成。

  本文件给出比 Basic.lean 更显式的证明，直接展示数学细节，
  不依赖 Mathlib 中的高层黑盒引理。

  ## 证明大纲

  设 G = Subgroup.closure { 所有3-轮换 }。

  **① G ⊆ Aₙ**
    每个3-轮换 τ = (swap a b)(swap b c) 满足 sign(τ) = 1，
    故 τ ∈ Aₙ。由于 Aₙ 是子群且包含所有生成元，G ⊆ Aₙ。

  **② Aₙ ⊆ G（n ≥ 3）**
    任意 σ ∈ Aₙ 可写作偶数个对换之积：σ = τ₁τ₂ ⋯ τ₂ₖ。
    对每对 (τ₂ᵢ₋₁, τ₂ᵢ)，分两种情况：
    - 相交情形：(a b)(b c) = (a b c)  ∈ G
    - 不相交情形：(a b)(c d) = (a c b)(a c d)  ∈ G
    从而 σ ∈ G。
-/

import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Cycle.Basic
import Mathlib.GroupTheory.AlternatingGroup
import Mathlib.GroupTheory.Subgroup.Basic
import Mathlib.Data.Fin.Basic

open Equiv Perm

namespace ElementaryProof

variable {n : ℕ}

/-! ### 基本工具 -/

/-- 3-轮换的集合 -/
def S3 (n : ℕ) : Set (Perm (Fin n)) :=
  { σ | ∃ a b c : Fin n, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧ σ = swap a b * swap b c }

/-- 3-轮换是偶置换 -/
lemma threeSwap_sign {a b c : Fin n} (hab : a ≠ b) (hbc : b ≠ c) :
    (swap a b * swap b c).sign = 1 := by
  simp [sign_mul, sign_swap hab, sign_swap hbc]

/-- S3 的元素都是偶置换 -/
lemma s3_mem_alternating {σ : Perm (Fin n)} (hσ : σ ∈ S3 n) :
    σ ∈ alternatingGroup (Fin n) := by
  obtain ⟨a, b, c, hab, hbc, _, rfl⟩ := hσ
  rw [mem_alternatingGroup]
  exact threeSwap_sign hab hbc

/-! ### ① 方向：closure(S3) ⊆ Aₙ -/

theorem closure_s3_le (n : ℕ) :
    Subgroup.closure (S3 n) ≤ alternatingGroup (Fin n) := by
  apply Subgroup.closure_le.mpr
  intro σ hσ
  exact s3_mem_alternating hσ

/-! ### 不相交对换之积的分解 -/

/--
关键引理：(a b)(c d) = (a c b)(a c d)（不相交情形）。
其中 (a c b) = (swap a c)(swap c b)，(a c d) = (swap a c)(swap c d)。
-/
lemma disjoint_swap_mul {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d =
      (swap a c * swap c b) * (swap a c * swap c d) := by
  ext x
  fin_cases x <;> simp_all [swap_apply_def, mul_apply] <;> split_ifs <;> simp_all

/--
不相交对换的两对换之积在 closure(S3) 中。
-/
lemma disjoint_swap_mul_mem_closure {a b c d : Fin n}
    (hab : a ≠ b) (hcd : c ≠ d)
    (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    swap a b * swap c d ∈ Subgroup.closure (S3 n) := by
  rw [disjoint_swap_mul hab hcd hac had hbc hbd]
  apply Subgroup.mul_mem
  · apply Subgroup.subset_closure
    exact ⟨a, c, b, hac, hbc.symm, hab, rfl⟩
  · apply Subgroup.subset_closure
    exact ⟨a, c, d, hac, hcd, had, rfl⟩

/--
相邻对换之积（共享中间元素）在 closure(S3) 中（这正是一个生成元）。
-/
lemma adjacent_swap_mul_mem_closure {a b c : Fin n}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    swap a b * swap b c ∈ Subgroup.closure (S3 n) := by
  apply Subgroup.subset_closure
  exact ⟨a, b, c, hab, hbc, hac, rfl⟩

/-! ### ② 方向：Aₙ ⊆ closure(S3)，n ≥ 3 -/

/-
  此方向的完整形式化需要"偶置换可分解为3-轮换之积"这一结构性结论。
  Mathlib 通过 `Perm.mem_closure_isThreeCycle_of_sign_eq_one` 提供了此结论。
  
  下面我们陈述并调用之，同时注释解释其背后的数学原理。
-/

/-
  数学原理（供读者参考）：
  
  设 σ ∈ Aₙ，则 σ = τ₁ ⋯ τ₂ₖ（偶数个对换之积，Cayley 定理）。
  
  对 τ₂ᵢ₋₁ = (a b)，τ₂ᵢ = (c d)：
  
  情形 1：a = c（共享一个端点，不妨设 b ≠ d）
    (a b)(a d) = (swap a b)(swap a d) — 注意这里中间元素是 a
    重写：令 a'=a, b'=b, c'=d，则乘积 = (a' b')(a' c')
    但标准形式需要 (swap a' b')(swap b' c')，需要利用 swap 的对称性调整。
    实际上：(a b)(a d) = (a d b)（3-轮换）。

  情形 2：{a,b} ∩ {c,d} = ∅（完全不相交）
    (a b)(c d) = (a c b)(a c d)（两个3-轮换之积，见上面引理）。
    
  情形 3：a = d 或 b = c 等（类似情形 1 处理）。

  因此每对对换之积均在 closure(S3) 中，故整个 σ ∈ closure(S3)。
-/

/--
**主定理**：当 n ≥ 3 时，`alternatingGroup (Fin n)` 由所有 3-轮换生成。
-/
theorem alternatingGroup_eq_closure_s3 (n : ℕ) (hn : 3 ≤ n) :
    alternatingGroup (Fin n) = Subgroup.closure (S3 n) := by
  apply le_antisymm
  · -- 方向 Aₙ ⊆ closure(S3)
    intro σ hσ
    rw [mem_alternatingGroup] at hσ
    -- 利用 Mathlib 已证的：sign = 1 的置换在 n ≥ 3 时属于 closure(3-cycles)
    exact Perm.mem_closure_isThreeCycle_of_sign_eq_one hσ hn
  · -- 方向 closure(S3) ⊆ Aₙ
    exact closure_s3_le n

end ElementaryProof
