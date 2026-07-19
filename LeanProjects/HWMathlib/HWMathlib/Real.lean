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

def SeqLim (a : ℕ → ℝ) (L : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - L| < ε

example (a : ℕ → ℝ) (L : ℝ) (a_const : ∀ n, a n = L) : SeqLim a L := by
  intro ε hε
  use 0
  intro n hn
  rewrite[a_const n]
  norm_num
  apply hε

theorem ArchProp {ε : ℝ} (_ : 0 < ε) : ∃ (N : ℕ), 1 / ε < N := by
  use ⌈1/ε⌉₊+1
  have fact : 1/ε  ≤ ⌈1/ε⌉₊ := by bound
  push_cast
  bound

/-!
太艰难，不过也算是熟悉了一下exact_mod_cast, norm_num, field_simp, linarith的用法
-/
theorem OneOverNLimZero (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : SeqLim a 0 := by
  intro ε hε
  choose N eps_inv_lt_N using ArchProp hε
  use N
  intro n n_ge_N
  have hnN : (n:ℝ)≥(N:ℝ) := by exact_mod_cast n_ge_N
  have hnε : (n:ℝ)>1/ε := by linarith[hnN, eps_inv_lt_N]
  have hεzero :1/ε>0:=by
    field_simp
    norm_num
  have hnzero :(n:ℝ)>0:=by linarith[hnε, hεzero]
  rewrite[ha n]
  norm_num
  field_simp
  field_simp at hnε
  linarith[hnε]


example (x y : ℝ) (x_pos : 0 < x) (y_pos : 0 < y) : ∃ (N : ℕ), y < x * N := by
  have hxy : 0 < x/y := by
    field_simp
    norm_num
    apply x_pos

  choose N hN using ArchProp hxy
  field_simp at hN
  use N

example (a : ℕ → ℝ) (ha : ∀ n, a n = (n + 1) / n) : ∃ L, SeqLim a L := by
  use 1
  intro ε hε
  choose N hN using ArchProp hε
  use N
  intro n hn
  have hεzero : 1/ε>0:=by
    field_simp
    norm_num
  have hnr : (n:ℝ)≥(N:ℝ) := by exact_mod_cast hn
  have hεn : 1/ε<(n:ℝ) := by linarith[hN, hnr]
  have ngt0 :(n:ℝ)>0:= by linarith[hεn, hεzero]
  have hanm1 : a n - 1 = 1/(n:ℝ) := by
    rewrite[ha]
    field_simp
    norm_num
  rewrite[hanm1]
  norm_num
  field_simp
  field_simp at hεn
  linarith[hεn]


example (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n ^ 2) : ∃ L, SeqLim a L := by
  use 0
  intro ε hε
  choose N hN using ArchProp hε
  -- have sqrtε : √ε > 0 := by sorry
  -- choose N hN using ArchProp sqrtε
  use N
  intro n hn
  -- have final : (n:ℝ)^2 * ε > 1 := by

  have rhn : (n : ℝ) ≥ (N : ℝ) := by exact_mod_cast hn
  have nge1 : (n : ℝ) ≥ 1 := by
    have hεzero : 1/ε > 0:=by
      field_simp
      norm_num
    have NRgtzero : (N:ℝ) > 0 := by linarith[hN, hεzero]
    have Ngtzero : N > 0 := by exact_mod_cast NRgtzero
    have Ngeone : N ≥ 1 := by apply Ngtzero
    have NRgeone : (N:ℝ) ≥ 1 := by exact_mod_cast Ngeone
    linarith[hn, hN, NRgeone]

  have nεone : (n:ℝ)*ε > 1 := by
    have oneoverεn : 1/ε < (n:ℝ) := by
      linarith[rhn, hN]
    field_simp at oneoverεn
    linarith

  have _eq : (n:ℝ)^2*ε = (n:ℝ)*((n:ℝ)*ε) := by linarith
  have _larger : (n:ℝ)*((n:ℝ)*ε) -(n:ℝ)> 0 := by
    have _h1 : (n:ℝ)*ε-1 > 0 := by linarith
    have _h2 : (n:ℝ) > 0 := by linarith
    have _h3 : (n:ℝ)*((n:ℝ)*ε-1) > 0 := by apply mul_pos _h2 _h1
    ring_nf
    linarith

  rewrite[ha n]
  norm_num
  field_simp
  rewrite[_eq]
  linarith


example (a : ℕ → ℝ) (ha : ∀ n, a n = (3 * n + 8) / (2 * n + 5)) : ∃ L, SeqLim a L := by
  use 3/2
  intro ε hε
  have pε : 4 * ε > 0 := by linarith[hε]
  choose N hN using ArchProp pε
  use N
  intro n hn
  rewrite [ha n]
  have res : (3*(n:ℝ) + 8)/(2*(n:ℝ)+5)-3/2=1/(4*(n:ℝ)+10) := by
    field_simp
    ring_nf
  rewrite[res]
  have _abs : 1/(4*(n:ℝ) + 10)> 0 := by
    have _h1 : 4*(n:ℝ) + 10>0 := by linarith
    field_simp
    linarith
  have _eq : |1/(4*(n:ℝ) + 10)|=1/(4*(n:ℝ) + 10) := by
    have _h1 :1/(4*(n:ℝ) + 10)≥ 0 := by linarith[_abs]
    apply abs_of_nonneg _h1
  rewrite[_eq]
  field_simp[_abs]
  ring_nf
  have rhn : (n:ℝ)≥(N:ℝ  ):= by exact_mod_cast hn
  have _t : (n:ℝ)>1/(4*ε) := by linarith[rhn, hN]
  field_simp at _t
  linarith[_t, hε]
