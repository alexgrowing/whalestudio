import Mathlib

set_option linter.style.emptyLine false

/-!
每种语法结构如何使用与证明
-/

-- 存在量词在条件中
-- 存在量词在结论中
-- 全称量词在条件中
-- 全称量词在结论中

example (x : U) (A B : Set U) (h1 : A ⊆ B) (h2 : x ∈ A) : x ∈ B := by
-- A ⊆ B本质上就是∀x ∈ A, x ∈ B，也就是∀x, x ∈ A → x ∈ B
  exact h1 h2

example (x : U) (A B C : Set U) (h1 : A ⊆ B) (h2 : B ⊆ C) (h3 : x ∈ A) : x ∈ C := by
-- h1 h3得到 x ∈ B，则h2 (h1 h3)就是 x ∈ C
  exact h2 (h1 h3)

example {x : U} {A B C : Set U} (h1 : A ⊆ B) (h2 : x ∈ B → x ∈ C) : x ∈ A → x ∈ C := by
-- 要证明的结论是 → 的结构，用intro可以把 → 前面的 x ∈ A拿出来作为该证明的条件，只需要证明 x ∈ C
  intro h
  exact h2 (h1 h)

example (A : Set U) : A ⊆ A := by
-- A ⊆ A本质上就是∀x, x ∈ A → x ∈ A，由于intro是提取 → 前面的内容作为条件
-- 因此有与前一条（只有一个Object）不同，此处的intro伴随两个Object
  intro x hx
  exact hx

example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
-- ¬A ⊆ B本质上就是A ⊆ B → False，因此使用intro hAB后，条件中多了A ⊆ B，结论变成了False
  intro hAB
-- x ∉ B本质就是x ∈ B → False，因此通过hAB h1得到x ∈ B后，h2作用上去就得到了False
  exact h2 (hAB h1)

-- 这是上一题另一种证明方法
example {A B : Set U} {x : U} (h1 : x ∈ A) (h2 : x ∉ B) : ¬A ⊆ B := by
  intro hAB
-- 此处执行apply h2后，要证明的结论从False变成了x ∈ B，这是怎么回事 TODO！！！
  apply h2
  exact hAB h1

example (A : Set U) (x : U) : x ∈ Aᶜ ↔ x ∉ A := by
  rfl








example {U : Type} (A : Set U) (h1 : ∀ F:Set (Set U), (⋃₀ F = A → A ∈ F)) :
    ∃ x, A = {x} := by
  let F : Set (Set U) := {S | ∃ x ∈ A, S = ({x} : Set U)}

  have hUnion : ⋃₀ F = A := by
    ext y
    constructor
    · intro hy
      rcases hy with ⟨S, hSF, hyS⟩
      rcases hSF with ⟨x, hxA, rfl⟩
      have hyx : y = x := by
        simpa using hyS
      rw [hyx]
      exact hxA
    · intro hyA
      exact ⟨{y}, ⟨y, hyA, rfl⟩, by simp⟩

  have hA : A ∈ F := h1 F hUnion
  rcases hA with ⟨x, _hxA, hAx⟩
  exact ⟨x, hAx⟩
