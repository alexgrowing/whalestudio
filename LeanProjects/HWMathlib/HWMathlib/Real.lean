import Mathlib

set_option linter.style.emptyLine false
set_option linter.style.whitespace false

section startup
/-!
  rcases 和 choose using 的效果感觉差不多 TODO
  ring_nf 和 ring 不知道有什么区别 TODO
  要证明的是个存在命题，不知道能不能用exact ⟨c, ?_⟩一句话了结了 TODO
-/
example (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  rcases h with ⟨c, hc⟩
  use c
  rewrite[hc]
  ring_nf

example (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  choose c hc using h
  use c
  rewrite[hc]
  ring

example (f : ℝ → ℝ) (h : ∃ c : ℝ, f c = 2) : ∃ x : ℝ, (f x) ^ 2 = 4 := by
  rcases h with ⟨c, hc⟩
  refine ⟨c, ?_⟩
  rw[hc]
  ring

end startup


example (g : ℝ → ℝ) (h1 : ∀ x, g (x + 1) = g (x) + 3) (h2 : g (0) = 5) : g (2) = 11 := by
  have h01 : g (0 + 1) = g 0 + 3 := h1 0
  have h12 : g (1 + 1) = g 1 + 3 := h1 1
  ring_nf at h01 h12
  rewrite [h01, h2] at h12
  ring_nf at h12
  exact h12
