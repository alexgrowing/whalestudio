import Mathlib

set_option linter.style.emptyLine false
set_option linter.style.whitespace false
set_option linter.style.longLine false

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

def SeqConv (a : ℕ → ℝ) : Prop := ∃ L, SeqLim a L

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


example (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) : ¬ SeqConv a := by
  rintro ⟨L, hL⟩
  rcases hL 1 (by norm_num) with ⟨N, hN⟩
  have h1 := hN N (le_refl N)
  have h2 := hN (N + 1) (Nat.le_succ N)
-- 居然可以直接rw[ha]，我还以为一定要 [ha N] 才可以替换 a N 呢
  rw[ha] at h1 h2
  rw[abs_lt] at h1 h2
  rcases Nat.even_or_odd N with heven | hodd
  · rw[heven.neg_one_pow] at h1
    rw[heven.add_one.neg_one_pow] at h2
    linarith
  · rw[hodd.neg_one_pow] at h1
    rw[hodd.add_one.neg_one_pow] at h2
    linarith

example (a : ℕ → ℝ) (ha2n : ∀ n, a (2 * n) = 3 - 1 / n) (ha2np1 : ∀ n, a (2 * n + 1) = 1 + 1 / n) : ¬ SeqConv a := by
  intro hsc
  choose L hL using hsc
  choose N hN using hL (1/2) (by norm_num)
  have h2n := hN (2*(N+3)) (by linarith)
  have h2np1 := hN (2*(N+3) + 1) (by linarith)

  have h_diff1 : |a (2*(N+3)) - a (2*(N+3)+1)| < 1 := by
    have _h1 : |a (2*(N+3)) - a (2*(N+3)+1)| = |(a (2*(N+3)) - L) + (L - a (2*(N+3)+1))| := by ring_nf
    have _h2 : |(a (2*(N+3)) - L) - (a (2*(N+3)+1) - L)| ≤  |a (2*(N+3)) - L| + |a (2*(N+3)+1) - L| := by apply abs_sub
    have _h3 : |(a (2*(N+3)) - L) - (a (2*(N+3)+1) - L)| = |(a (2*(N+3)) - L) + (L - a (2*(N+3)+1))| := by ring_nf
    linarith[_h1, _h2, _h3, h2n, h2np1]

  have h_diff2 : |a (2*(N+3)) - a (2*(N+3)+1)| ≥ 1 := by
    have _h1 : a (2*(N+3)) = 3 - 1/(N+3) := by rewrite[ha2n  (N+3)]; push_cast;rfl
    have _h2 : a (2*(N+3)+1) = 1 + 1/(N+3) := by rewrite[ha2np1 (N+3)]; push_cast;rfl
    rewrite[_h1, _h2]
    have _h3 : 3-1/((N:ℝ)+3)-(1+1/((N:ℝ)+3)) ≥ 0 := by field_simp;norm_num;linarith
    have _h4 : |3-1/((N:ℝ)+3)-(1+1/((N:ℝ)+3))| = 3-1/((N:ℝ)+3)-(1+1/((N:ℝ)+3)) := by apply abs_of_nonneg _h3
    rewrite[_h4]
    field_simp
    have _h5 : 2*(N:ℝ)+4 ≥ (N:ℝ)+4 := by linarith
    linarith

  linarith


example (a b : ℕ → ℝ) (L : ℝ) (h : SeqLim a L) (b_scaled : ∀ n, b n = 2 * a n) : SeqLim b (2 * L) := by
  intro ε hε
  rcases h (ε/2) (by linarith) with ⟨N, hN⟩
  use N
  intro n hn
  rewrite[b_scaled]
  have res : |2 * a n - 2 * L| = 2 * |(a n - L)| := by
    have _h1 : |2 * a n - 2 * L| = |2 * (a n - L)| := by ring_nf
    have _h2 : |2 * (a n - L)| = |2| * |a n - L| := by apply abs_mul
    have _h3 : 0 ≤ (2:ℝ) := by linarith
    have _h4 : |(2:ℝ)| = 2 := by apply abs_of_nonneg _h3
    rewrite[_h1, _h2, _h4]
    rfl
  rewrite[res]
  linarith[hN n hn]


theorem SumLim (a b c : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L) (hb : SeqLim b M) (hc : ∀ n, c n = a n + b n) : SeqLim c (L + M) := by
  intro ε hε
  choose Na hNa using ha (ε/2) (by linarith[hε])
  choose Nb hNb using hb (ε/2) (by linarith[hε])
  use Na + Nb
  intro n hn
  rewrite[hc]
  have _h1 : |a n + b n - (L + M)| = |a n - L + (b n - M)| := by ring_nf
  have _h2 : |a n - L + (b n - M)| ≤ |a n - L| + |b n - M| := by apply abs_add_le
  have _h3 : |a n - L| < ε/2 := hNa n (by linarith[hn])
  have _h4 : |b n - M| < ε/2 := hNb n (by linarith[hn])
  linarith[_h1, _h2, _h3, _h4]


example (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) : ∃ N, ∀ n ≥ N, a n ≥ L - 1 := by
  rcases ha 1 (by linarith) with ⟨N, hN⟩
  use N
  intro n hn
  have _h1 := hN n hn
  rewrite[abs_lt] at _h1
  linarith

example (a b c : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (cToL : SeqLim c L) (aLeb : ∀ n, a n ≤ b n) (bLec : ∀ n, b n ≤ c n) : SeqLim b L := by
  intro ε hε
  rcases aToL ε hε with ⟨Na, hNa⟩
  rcases cToL ε hε with ⟨Nb, hNb⟩
  use Na + Nb
  intro n hn
  specialize aLeb n
  specialize bLec n
  specialize hNa n (by linarith[hn])
  specialize hNb n (by linarith[hn])
  rewrite[abs_lt] at hNa hNb
  have _h1 : b n - L <  ε := by linarith
  have _h2 : b n - L > - ε := by linarith
  rewrite[abs_lt]
  exact ⟨_h2, _h1⟩

example (a : ℕ → ℝ) (ha : ∀ N, ∃ n ≥ N, |a n| > 10) : ¬ ∃ L, |L| < 5 ∧ SeqLim a L := by
  intro h
  rcases h with ⟨L, ⟨hL, hLim⟩⟩
  rcases hLim 1 (by linarith) with ⟨N, hN⟩
  rcases ha N with ⟨n, ⟨hn, han⟩⟩
  have _hN := hN n hn
  have hdiff1 : |a n| < 6 := by
    have _h1 : |a n| = |a n - L + L| := by norm_num
    have _h2 : |a n - L + L| ≤ |a n - L| + |L| := by apply abs_add_le
    linarith
  linarith


example (a : ℕ → ℝ) (L M : ℝ) (aToL : SeqLim a L) (aToM : SeqLim a M) : L = M := by
  by_contra h
  let ε := |L - M| / 3
  have _hε : ε = |L - M|/3 := by rfl
  have hε : ε > 0 := by positivity
    -- have _h1 : L - M ≠ 0 := by
    --   by_contra _h11
    --   have _h12 : L = M := by linarith
    --   apply h _h12
    -- have _h2 : |L - M| > 0 := by apply abs_pos.mpr _h1
    -- linarith
  rcases aToL ε hε with ⟨NL, hNL⟩
  rcases aToM ε hε with ⟨NM, hNM⟩
  have _hNL := hNL (NL+NM) (by linarith)
  have _hNM := hNM (NL+NM) (by linarith)
  have hdiff : |L-M|<2*ε := by
    have _h1 : |L-M| = |L - a (NL+NM) + (a (NL+NM) - M)| := by norm_num
    have _h2 : |L - a (NL+NM) + (a (NL+NM) - M)| ≤ |L - a (NL+NM)| + |a (NL+NM) - M| := by apply abs_add_le
    have _h3 : |L - a (NL+NM)| = |-(a (NL+NM) - L)| := by norm_num
    have _h4 : |-(a (NL+NM) - L)| = |a (NL+NM) - L| := by apply abs_neg
    linarith
  rewrite[_hε] at hdiff
  linarith
