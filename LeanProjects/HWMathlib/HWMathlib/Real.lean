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

def SeqBdd {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) := ∃ M > 0, ∀ n, |a n| ≤ M

def SeqBddBy (a : ℕ → ℝ) (M : ℝ) := ∀ n, a n ≤ M

def Subseq (σ : ℕ → ℕ) := ∀ i j, i < j → σ i < σ j

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

theorem EventuallyGeHalfLimPos (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (LneZero: L ≠ 0) : ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a (n)| := by
  have hε : |L|/2 > 0 := by
    have _h1 : |L| > 0 := by apply abs_pos.mpr LneZero
    linarith
  rcases aToL (|L|/2) (hε) with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  have _r1 : |L| = |(L - a n) + a n| := by norm_num
  have _r2 : |(L - a n) + a n| ≤ |L - a n| + |a n| := by apply abs_add_le
  have _r3 : |L - a n| = |-(a n - L)| := by norm_num
  have _r4 : |-(a n - L)| = |a n - L| := by apply abs_neg
  linarith

example (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) (LneZero : L ≠ 0) (b : ℕ → ℝ) (bEqInva : ∀ n, b n = 1 / a n) : SeqLim b (1 / L) := by
  intro ε hε
  have _h1 : |L| > 0 := by apply abs_pos.mpr LneZero
  have _h := aToL (ε*|L|^2/2) (by positivity)
  choose N₁ hN₁ using _h
  choose N₂ hN₂ using EventuallyGeHalfLimPos a L aToL
  use (N₁ + N₂ LneZero)
  intro n hn
  specialize bEqInva n
  specialize hN₁ n (by linarith)
  specialize hN₂ LneZero n (by linarith)
  rewrite[bEqInva]
  have _ha_n_not_zero : a n ≠ 0 := by
    have _h2 : |L|/2 > 0 := by linarith
    have _h3 : |a n| > 0 := by linarith
    apply abs_pos.mp _h3

  have _eq1 : 1/(a n) - 1/L = (L - a n)/(L * a n) := by
    field_simp[LneZero, _ha_n_not_zero]
  have _eq2 : |(L - a n)/(L * a n)| = |L - a n|/|L * a n| := by apply abs_div
  have _eq3 : |L * a n| = |L| * |a n| := by apply abs_mul
  have _eq4 : |L| * (|L|/2) ≤ |L| * |a n| := by bound
  rewrite[_eq1, _eq2, _eq3]
  field_simp

  have _r1 : |L - a n| = |-(a n - L)| := by norm_num
  have _r2 : |-(a n - L)| = |a n - L| := by apply abs_neg
  rewrite[_r1, _r2]
  nlinarith

theorem EventuallyGeHalfLim (a : ℕ → ℝ) (L : ℝ) (aToL : SeqLim a L) : ∃ N, ∀ n ≥ N, |L| / 2 ≤ |a (n)| := by
  by_cases hL : L = 0
  · rewrite[hL]
    norm_num
  · exact EventuallyGeHalfLimPos a L aToL hL

theorem EventuallyBdd_of_SeqConv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (hL : L ≠ 0) : ∃ N, ∀ n ≥ N, |a n| ≤ 2 * |L| := by
  rcases ha |L| (by positivity) with ⟨N, hN⟩
  use N
  intro n hn
  specialize hN n hn
  have _r1 : |a n| = |a n - L + L| := by norm_num
  have _r2 : |a n - L + L| ≤ |a n - L| + |L| := by apply abs_add_le
  linarith

example (a b : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L) (hb : SeqLim b M) (hLM : L < M) : ∃ N, ∀ n ≥ N, a n < b n := by
  rcases ha ((M-L)/2) (by linarith) with ⟨Na, hNa⟩
  rcases hb ((M-L)/2) (by linarith) with ⟨Nb, hNb⟩
  use (Na + Nb)
  intro n hn
  specialize hNa n (by linarith)
  specialize hNb n (by linarith)
  rewrite[abs_lt] at hNa hNb
  linarith

theorem IdLeTwoPow (n : ℕ) : n < 2 ^ n := by
  induction n with
  | zero =>
      linarith
  | succ k hk =>
      rewrite[pow_succ]
      linarith

open Finset

theorem TermLeSum {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (N : ℕ) : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by
  induction N with
    |zero =>
      intro n hn
      contradiction
    |succ M hM =>
      intro n hn
      rewrite[Finset.sum_range_succ]
      have _h1 :  |a M| + ∑ x ∈ Finset.range M, |a x| ≥ ∑ k ∈ Finset.range M, |a k| := by
        bound
      by_cases hc : n < M
      · specialize hM n hc
        bound
      · have _hn : n = M := by bound
        rewrite[_hn]
        have _h2 : ∑ x ∈ Finset.range M, |a x| ≥ 0 := by
          apply Finset.sum_nonneg
          intro i hi
          bound
        bound

theorem Bdd_of_ConvNonzero (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (hL : L ≠ 0) : SeqBdd a := by
  rcases EventuallyBdd_of_SeqConv a L ha hL with ⟨N, hN⟩
  have hLeN := TermLeSum a N
  have _h1 : |L| > 0 := by apply abs_pos.mpr hL
  have _h2 : ∑ k ∈ range N , |a k| ≥ 0 := by
    apply Finset.sum_nonneg
    intro i hi
    bound
  use 2 * |L| + ∑ k ∈ range N, |a k|
  split_ands
  · bound
  · intro n
    by_cases hc : n ≥ N
    · specialize hN n hc
      bound
    · specialize hLeN n (by linarith)
      bound

theorem ProdLimNeNe (a b c : ℕ → ℝ) (L M : ℝ) (hL : L ≠ 0) (hM : M ≠ 0) (ha : SeqLim a L) (hb : SeqLim b M) (hc : ∀ n, c n = a n * b n): SeqLim c (L * M) := by
  intro ε hε
  rcases Bdd_of_ConvNonzero b M hb hM with ⟨K, ⟨hK, hbn⟩⟩
  rcases ha (ε/(2*K)) (by field_simp; linarith) with ⟨Na, hNa⟩
  rcases hb (ε/(2*|L|)) (by field_simp; linarith) with ⟨Nb, hNb⟩
  use Na + Nb
  intro n hn
  specialize hc n
  specialize hbn n
  specialize hNa n (by linarith)
  specialize hNb n (by linarith)
  have _h1 : |a n * b n - L * b n| < (ε/2) := by
    calc
      |a n * b n - L * b n| = |(a n - L) * b n| := by ring_nf
      _ = |a n - L| * |b n| := by apply abs_mul
      _ ≤ |a n - L| * K := by bound
      _ < ε / (2 * K) * K := by bound
      _ = ε / 2 := by field_simp
  have _h2 : |L * b n - L * M| < (ε/2) := by
    calc
      |L * b n - L * M| = |L * (b n - M)| := by ring_nf
      _ = |L| * |b n - M| := by apply abs_mul
      _ < |L| * (ε / (2 * |L|)) := by bound[abs_pos.mpr hL]
      _ = ε / 2 := by field_simp
  have r : |c n - L * M| < ε := by
    calc
      |c n - L * M| = |a n * b n - L * M| := by rewrite[hc];rfl
      _ = |a n * b n - L * b n + L * b n - L * M| := by ring_nf
      _ = |(a n * b n - L * b n) + (L * b n - L * M)| := by ring_nf
      _ ≤ |a n * b n - L * b n| + |L * b n - L * M| := by apply abs_add_le
      _ < (ε / 2) + (ε / 2) := by bound
      _ = ε := by ring_nf
  apply r


theorem OrderLimLe (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (K : ℝ) (hK : SeqBddBy a K) : L ≤ K := by
  by_contra hc
  push Not at hc
  rcases ha ((L-K)/2) (by linarith) with ⟨N, hN⟩
  have haL := hN N (by linarith)
  have haK := hK N
  rewrite[abs_lt] at haL
  have hdiff : a N > K := by linarith
  bound

theorem SubseqGe (σ : ℕ → ℕ) (hσ : ∀ i, ∀ j, i < j → σ i < σ j) (n : ℕ) : n ≤ σ n := by
  induction n with
  | zero => bound
  | succ k hk =>
    have h1 : σ (k + 1) > σ k := by apply hσ; bound
    have h2 : σ (k + 1) ≥ σ k + 1 := by bound
    bound

theorem SubseqConv (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (σ : ℕ → ℕ) (hσ : Subseq σ) : SeqLim (a ∘ σ) L := by
  intro ε hε
  rcases ha ε hε with ⟨N, hN⟩
  use N
  intro n hn
  have _h : n ≤ σ n := by apply SubseqGe σ hσ n
  have h : σ n ≥ N := by linarith[hn, _h]
  specialize hN (σ n) h
  apply hN

example (a : ℕ → ℝ) (ha : ∀ n, a n = (-1) ^ n) : ∃ σ L, Subseq σ ∧ SeqLim (a ∘ σ) L := by
  let σ : ℕ → ℕ := fun n ↦ 2 * n
  use σ, 1
  split_ands
  · intro i j hij
    have _hi : σ i = 2 * i := by bound
    have _hj : σ j = 2 * j := by bound
    rewrite[_hi, _hj]
    bound
  · intro ε hε
    use 1
    intro n hn
    have haσ : (a ∘ σ) n = 1 := by
      calc
        (a ∘ σ) n = a (σ n) := by bound
        _ = a (2 * n) := by bound
        _ = (-1) ^ (2 * n) := by bound
        _ = 1 := by bound
    have _hr : (a ∘ σ) n - 1 = 0 := by bound
    have hr : |(a ∘ σ) n - 1| = 0 := by apply abs_eq_zero.mpr _hr
    bound


theorem LimZeroTimesBdd (a b c : ℕ → ℝ) (ha : SeqLim a 0) (hb : SeqBdd b) (hc : ∀ n, c n = a n * b n) : SeqLim c 0 := by
  intro ε hε
  rcases hb with ⟨M, ⟨hM, LbM⟩⟩
  rcases ha (ε/M) (by bound) with ⟨N, han⟩
  use N
  intro n hn
  specialize han n hn
  have _eq : |a n - 0| = |a n| := by bound
  rewrite[_eq] at han
  specialize hc n
  specialize LbM n
  calc
    |c n - 0| = |c n| := by bound
    _ = |a n * b n| := by rewrite[hc]; rfl
    _ = |a n| * |b n| := by apply abs_mul
    _ ≤ |a n| * M := by bound
-- TODO 为什么下面可以直接变成 < ？
    _ < (ε/M) * M := by bound
    _ = ε := by field_simp

theorem ProdLim (a b c : ℕ → ℝ) (L M : ℝ) (ha : SeqLim a L) (hb : SeqLim b M) (hc : ∀ n, c n = a n * b n): SeqLim c (L * M) := by
  by_cases h : L ≠ 0 ∧ M ≠ 0
  · apply ProdLimNeNe a b c L M h.left h.right ha hb hc
  · push Not at h
    by_cases hL : L ≠ 0
    · have _hc : ∀ (n : ℕ), c n = b n * a n := by
        intro n
        have _h := hc n
        bound
      have hM := h hL
      rewrite[hM] at hb
      have hLM : L * M = 0 := by bound
      rewrite[hLM]
      have haBdd := Bdd_of_ConvNonzero a L ha hL
      apply LimZeroTimesBdd b a c hb haBdd _hc
    · push Not at hL
      rewrite[hL] at ha
      have hLM : L * M = 0 := by bound
      rewrite[hLM]
      by_cases hM : M ≠ 0
      · have hbBdd := Bdd_of_ConvNonzero b M hb hM
        apply LimZeroTimesBdd a b c ha hbBdd hc
      · push Not at hM
        rewrite[hM] at hb
        intro ε hε
        rcases ha (ε/2) (by bound) with ⟨Na, hNa⟩
        rcases hb 1 (by linarith) with ⟨Nb, hNb⟩
        use Na + Nb
        intro n hn
        specialize hNa n (by bound)
        specialize hNb n (by bound)
        specialize hc n
        calc
          |c n - 0| = |c n| := by bound
          _ = |a n * b n| := by rewrite[hc];rfl
          _ = |a n| * |b n| := by apply abs_mul
          _ = |a n - 0| * |b n - 0| := by bound
-- TODO 这里为什么不能变成 < 呢？只能是 ≤ ?对比上一个 TODO
          _ ≤ (ε / 2) * 1 := by bound
          _ < ε := by bound

theorem OrderLimGt (a : ℕ → ℝ) (L : ℝ) (ha : SeqLim a L) (K : ℝ) (hK : ∀ n, K < a n) : K ≤ L := by
  by_contra h
  push Not at h
  rcases ha ((K-L)/2) (by bound) with ⟨N, hN⟩
  specialize hN N (by bound)
  specialize hK N
  rewrite[abs_lt] at hN
  bound

example : ∃ a, SeqLim a 0 ∧ ∀ n, 0 < a n := by
  let a : ℕ → ℝ := fun n ↦ 1/(n+1)
  have ha : ∀ n, a n = 1/(n+1) := by intro n;rfl
  use a
  split_ands
  · intro ε hε
    rcases ArchProp hε with ⟨N, hN⟩
    use N
    intro n hn
    have _hn : (n:ℝ) ≥ (N:ℝ) := by exact_mod_cast hn
    specialize ha n
    calc
      |a n - 0| = |a n| := by bound
      _ = |1 / ((n:ℝ) + 1)| := by rewrite[ha];rfl
      _ = 1 / ((n:ℝ) + 1) := by
        have _h1 : (n:ℝ) + 1 > 0 := by bound
        have _h2 : 1/((n:ℝ)+1) ≥ 0 := by bound
        apply abs_of_nonneg _h2
      _ ≤ 1 / ((N:ℝ) + 1) := by bound
      _ < ε := by
        have _h : 1/ε < (N:ℝ) +1 := by bound
        field_simp at _h
        ring_nf at _h
        field_simp
        ring_nf
        bound
  · intro n
    specialize ha n
    rewrite[ha]
    have h1: (n+1:ℝ) > 0 := by bound
    bound

example (a : ℕ → ℝ) (ha : ∀ n, a n = n) : ¬ SeqBdd a := by
  intro h
  rcases h with ⟨M, ⟨hM, han⟩⟩
  let m : ℕ := Nat.ceil M + 1
  have _hmgt0 : m ≥ 0 := by bound
  have hmgt0 : (m:ℝ) ≥ 0 := by exact_mod_cast _hmgt0
  have _abs : |(m:ℝ)| = m := by apply abs_of_nonneg hmgt0
  have hm : m > M := by
    have _h1 : Nat.ceil M ≥ M := by exact_mod_cast Nat.le_ceil M
    have _h2 : m = Nat.ceil M + 1 := by bound
    have _h3 : (m:ℝ) = Nat.ceil M + 1 := by exact_mod_cast _h2
    bound
  specialize ha m
  specialize han m
  rewrite[ha, _abs] at han
  bound

theorem Diverge_of_DiffSubseqLim (a : ℕ → ℝ) (σ τ : ℕ → ℕ) (σsub : Subseq σ) (τsub : Subseq τ) (L M : ℝ) (hσ : SeqLim (a ∘ σ) L) (hτ : SeqLim (a ∘ τ) M) (hLM : L ≠ M) : ¬ SeqConv a := by
  intro h
  rcases h with ⟨F, hf⟩
  let ε : ℝ := |L - M| / 4
  have iε : ε = |L-M|/4 := by bound
  have hε : ε > 0 := by
    have _h1 : L - M ≠ 0 := by bound
    have _h2 : |L - M| > 0 := by apply abs_pos.mpr _h1
    bound
  rcases hf ε hε with ⟨N, hN⟩
  rcases hσ ε hε with ⟨Nσ, hNσ⟩
  rcases hτ ε hε with ⟨Nτ, hNτ⟩

  let S : ℕ := N + Nσ + Nτ
  have iS : S = N + Nσ + Nτ := by bound
  specialize hNσ S (by bound)
  have hdiff1 : F < L + 2*ε ∧ F > L - 2*ε := by
    have _h1 : S ≤ σ S := by apply SubseqGe σ σsub
    have _hNσ1 : |a (σ S) - L| < ε := by bound
    have _hNσ2 : |a (σ S) - F| < ε := hN (σ S) (by bound)
    rewrite[abs_lt] at _hNσ1 _hNσ2
    bound
  have hdiff2 : F < M + 2*ε ∧ F > M - 2*ε := by
    have _h1 : S ≤ τ S := by apply SubseqGe τ τsub
    have _hNτ1 : |a (τ S) - M| < ε := by bound
    have _hNτ2 : |a (τ S) - F| < ε := hN (τ S) (by bound)
    rewrite[abs_lt] at _hNτ1 _hNτ2
    bound
  by_cases h : L > M
  · have _h1 : L - M ≥ 0 := by bound
    have _h2 : |L - M| = L - M := by apply abs_of_nonneg _h1
    have _h3 : F > L/2 + M/2 := by
      calc
        F > L - 2*ε := by apply hdiff1.right
        _ = L - 2*((L-M)/4) := by rewrite[iε, _h2];rfl
        _ = L/2 + M/2 := by bound
    have _h4 : F < L/2 + M/2 := by
      calc
        F < M + 2*ε := by apply hdiff2.left
        _ = M + 2*((L-M)/4) := by rewrite[iε, _h2];rfl
        _ = L/2 + M/2 := by bound
    bound
  · push Not at h
    have _h1 : L - M < 0 := by
      by_contra _h11
      push Not at _h11
      have _h12 : L - M = 0 := by bound
      bound
    have _h2 : |L - M| = -(L - M) := by apply abs_of_neg _h1
    have _h3 : F > L/2+M/2 := by
      calc
        F > M - 2*ε := by apply hdiff2.right
        _ = M - 2*((-(L-M))/4) := by rewrite[iε, _h2];rfl
        _ = L/2+M/2 := by bound
    have _h4 : F <L/2+M/2 := by
      calc
        F < L + 2*ε := by apply hdiff1.left
        _ = L + 2*((-(L-M))/4) := by rewrite[iε, _h2];rfl
        _ = L/2 + M/2 := by bound
    bound

def IsCauchy{X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) : Prop := ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε

theorem IsCauchy_of_SeqConv {a : ℕ → ℝ} (ha : SeqConv a) : IsCauchy a := by
  intro ε hε
  rcases ha with ⟨L, hL⟩
  rcases hL (ε/2) (by bound) with ⟨N, hN⟩
  use N
  intro n hn m hm
  have han : |a n - L| < (ε/2) := hN n hn
  have ham : |a m - L| < (ε/2) := hN m (by bound)
  calc
    |a m - a n| = |(a m - L) + (L - a n)| := by bound
    _ ≤ |a m - L| + |L - a n| := by apply abs_add_le
    _ = |a m - L| + |a n - L| := by
      have _h : |L - a n| = |a n - L| := by apply abs_sub_comm
      rewrite[_h]
      rfl
    _ < ε := by bound

theorem IsCauchy_of_Sum {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a b : ℕ → X) (ha : IsCauchy a) (hb : IsCauchy b) : IsCauchy (a + b) := by
  intro ε hε
  rcases ha (ε/2) (by bound) with ⟨M, hM⟩
  rcases hb (ε/2) (by bound) with ⟨N, hN⟩
  use M + N
  intro n hn m hm
  specialize hM n (by bound) m hm
  specialize hN n (by bound) m hm
  calc
    |(a + b) m - (a + b) n| = |a m + b m - (a n + b n)| := by bound
    _ = |(a m - a n) + (b m - b n)| := by ring_nf
    _ ≤ |a m - a n| + |b m - b n| := by apply abs_add_le
    _ < ε := by bound

theorem IsBdd_of_Cauchy {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : IsCauchy a) : SeqBdd a := by
  rcases ha 1 (by bound) with ⟨N, hN⟩
  have hGeN := hN N (by bound)
  have hLtN : ∀ n < N, |a n| ≤ ∑ k ∈ range N, |a k| := by
    intro n hn
    apply TermLeSum a N n hn
  use |a N| + 1 + ∑ k ∈ range N, |a k|
  have _h1 : |a N| ≥ 0 := by bound
  have _h2 : |a N| + 1 > 0 := by bound
  have _h3 : ∑ k ∈ range N , |a k| ≥ 0 := by
    apply sum_nonneg
    intro i hi
    bound
  split_ands
  · bound
  · intro n
    by_cases hn : n ≥ N
    · specialize hGeN n hn
      calc
        |a n| = |a n - a N + a N| := by bound
        _ ≤ |a n - a N| + |a N| := by apply abs_add_le
        _ ≤ 1 + |a N| := by bound
        _ = |a N| + 1 := by bound
        _ ≤ |a N| + 1 + ∑ k ∈ range N, |a k| := by bound
    · push Not at hn
      specialize hLtN n hn
      bound

example (a : ℕ → ℝ) (ha : ∀ n, a n = n) : ¬ ∃ σ, Subseq σ ∧ SeqConv (a ∘ σ) := by
  intro h
  rcases h with ⟨σ, ⟨hsub, hcon⟩⟩
  rcases hcon with ⟨L, hL⟩
  rcases hL 1 (by bound) with ⟨N, hN⟩
  let M := Nat.ceil L + 2
  have hML : M > L + 1 := by
    have _h1 : Nat.ceil L ≥ L := by apply Nat.le_ceil L
    have _h2 : Nat.ceil L + 2 > L + 1 := by bound
    have _h3 : M = Nat.ceil L + 2 := by bound
    have _h4 : (M:ℝ) = Nat.ceil L + 2 := by exact_mod_cast _h3
    bound
  have hM : M = Nat.ceil L + 2 := by bound
  have hdiff1 : (a ∘ σ) (M + N) > L + 1 := by
    have _h1 : σ (M + N) ≥ (M + N) := by apply SubseqGe σ hsub (M + N)
    calc
      (a ∘ σ) (M + N) = a (σ (M + N)) := by bound
      _ = σ (M + N) := by bound
      _ ≥ M + N := by exact_mod_cast _h1
      _ ≥ M := by bound
      _ > L + 1 := by bound
  have hdiff2 : (a ∘ σ) (M + N) ≤ L + 1 := by
    specialize hN (M + N) (by bound)
    rewrite[abs_lt] at hN
    bound
  bound

theorem subseq_of_succ (σ : ℕ → ℕ) (hσ : ∀ n, σ n < σ (n + 1)) : Subseq σ := by
  intro i j h
  have _h1 : ∀ k m : ℕ, σ k < σ (k +(m + 1)) := by
    intro k m
    induction m with
    |zero =>
      bound
    |succ m hm =>
      calc
        σ (k + (m + 1 + 1)) = σ (k + m + 1 + 1) := by bound
        _ > σ (k + m + 1) := by bound
        _ > σ (k) := by bound
-- TODO 又多了一个omega，不知道omega, bound, linarith, norm_num, simp之间的区别
  have _h2 : j = i + ((j - i - 1) + 1) := by omega
  rewrite[_h2]
  apply _h1 i (j - i - 1)

theorem succ_iterate (σ : ℕ → ℕ) (k n : ℕ) : σ (σ^[k] n) = σ^[k + 1] n := by
  have h1 : σ^[k+1] n = σ (σ^[k] n) := by
    simp [Function.iterate_succ_apply']
  bound

theorem Subseq_of_Iterate (σ : ℕ → ℕ) (hσ : ∀ n, n < σ n) (n₀ : ℕ) : Subseq (fun n ↦ σ^[n] n₀) := by
  apply subseq_of_succ
  intro n
  rewrite[← show σ (σ^[n] n₀) = σ^[n+1] n₀ by apply succ_iterate σ n n₀]
  bound

example (p : ℕ → Prop) (h : ∀ N, ∃ n > N, p n) : ∃ σ, Subseq σ ∧ ∀ n, p (σ n) := by
-- TODO choose居然还能这么用，rcases在这里就用不了了
  choose τ hf1 hf2 using h
  let σ : ℕ → ℕ := fun n ↦ τ^[n] (τ 0)
  have hσ0 : σ 0 = τ 0 := by rfl
  have hσsucc : ∀ n, σ (n + 1) = τ (σ n) := by
    intro n
-- TODO 这里change的用法，改变goal
    change τ^[n+1] (τ 0) = τ (τ^[n] (τ 0))
-- TODO 这里Function复合替换的用法
    rw[Function.iterate_succ_apply']
  use σ
  split_ands
  · apply Subseq_of_Iterate τ hf1 (τ 0)
  · intro n
    induction n with
    | zero =>
      rw[hσ0]
      apply hf2 0
    | succ n _ =>
-- 虽然用了递归，但却不需要用到假设的条件，神奇
      rw[hσsucc]
      apply hf2 (σ n)



theorem IterateGap {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : Monotone a) (ε : X) (_ : ε > 0) (τ : ℕ → ℕ) (hτ : ∀ n, τ n ≥ n) (σ : ℕ → ℕ) (hσ : ∀ n, σ n ≥ τ n) (hgap : ∀ n, ε ≤ |a (σ n) - a (τ n)|) : ∀ (k : ℕ), k * ε ≤ a (σ^[k] 0) - a 0 := by
  intro k
  induction k with
  | zero => bound
  | succ k hk =>
    have _h1 : a (σ^[k + 1] 0) = a (σ (σ^[k] 0)) := by rewrite[Function.iterate_succ_apply'];rfl
    rewrite[_h1]
    have _ha : ∀ i j, i ≤ j → a i ≤ a j := by apply ha
    specialize hτ (σ^[k] 0)
    specialize hσ (σ^[k] 0)
    have _h2 : σ (σ^[k] 0) ≥ σ^[k] 0 := by bound
    have _h3 := _ha (τ (σ^[k] 0)) (σ (σ^[k] 0)) hσ
    have _h4 : a (σ (σ^[k] 0)) - a (τ (σ^[k] 0)) ≥ 0 := by bound
    have _h5 : |a (σ (σ^[k] 0)) - a (τ (σ^[k] 0))| = a (σ (σ^[k] 0)) - a (τ (σ^[k] 0)) := by apply abs_of_nonneg _h4
    specialize hgap (σ^[k] 0)
    have _h6 : a (σ (σ^[k] 0)) - a (τ (σ^[k] 0)) ≥ ε := by rewrite[_h5] at hgap;bound
    have _h7 := _ha (σ^[k] 0) (τ (σ^[k] 0)) hτ
    have _h8 : a (σ (σ^[k] 0)) - a (σ^[k] 0) ≥ ε := by bound
    have _h9 : a (σ (σ^[k] 0)) - a 0 ≥ a (σ^[k] 0) - a 0 + ε := by bound
    have _h10 : k * ε + ε ≤ a (σ (σ^[k] 0)) - a 0 := by bound
    have _h11 : (k + 1) * ε = k * ε + ε := by ring_nf
    have _h12 : (k + 1) * ε ≤ a (σ (σ^[k] 0)) - a 0 := by bound
    exact_mod_cast _h12

theorem IsCauchy_of_MonotoneBdd {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] {a : ℕ → X} {M : X} (ha : Monotone a) (hM : ∀ n, a n ≤ M) : IsCauchy a := by
  change ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε
  by_contra h
  push Not at h
  rcases h with ⟨ε, ⟨hε, hCauchy⟩⟩
  choose f1 hf1 f2 hf2 hf3 using hCauchy
  let T := Nat.ceil ((M + 1 - a 0)/ε)
  have vT : T = Nat.ceil ((M + 1 - a 0)/ε) := by bound
  have _h := IterateGap a ha ε hε f1 hf1 f2 hf2 hf3 T
  have r : a (f2^[T] 0) > M := by
    calc
      a (f2^[T] 0) ≥ T * ε + a 0 := by bound[_h]
      _ = Nat.ceil ((M + 1 - a 0)/ε) * ε + a 0 := by rewrite[vT];rfl
      _ ≥ ((M + 1 - a 0)/ε) * ε + a 0 := by bound
      _ > ((M - a 0)/ε) * ε + a 0 := by bound
      _ = (M - a 0) + a 0 := by field_simp
      _ = M := by bound
  specialize hM (f2^[T] 0)
  bound

def IsAPeak {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (n : ℕ) := ∀ m > n, a m ≤ a n

def UnBddPeaks {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) := ∀ k, ∃ n > k, IsAPeak a n

theorem MonotoneSubseq_of_BddPeaks {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : ¬ UnBddPeaks a) : ∃ σ, Subseq σ ∧ Monotone (a ∘ σ) := by
  unfold UnBddPeaks IsAPeak at ha
  push Not at ha
  rcases ha with ⟨K, hK⟩
  have hK' : ∀ n, ∃ m, n > K → (m > n ∧ a n < a m) := by
    intro n
    by_cases hn : n > K
    · rcases hK n hn with ⟨m, hm⟩
      exact ⟨m, fun _ => hm⟩
    · exact ⟨n + 1, fun h => absurd h hn⟩
    --   use m
    --   intro hn'
    --   exact hm
    -- · use n + 1
    --   intro hn'
    --   bound

  choose f hf1 hf2 using hK'
  let σ : ℕ → ℕ := fun n ↦ f^[n] (K + 1)
  have hσ : ∀ n, σ n > K := by
    intro n
    induction n with
    | zero =>
      calc
        σ 0 = K + 1 := by bound
        _ > K := by bound
    | succ n hn =>
      calc
        σ (n + 1) = f^[n+1] (K + 1) := by bound
        _ = f (f^[n] (K + 1)) := by rewrite[Function.iterate_succ_apply'];rfl
        _ = f (σ n) := by bound
        _ > σ n := by bound
        _ > K := by bound

  have hr : ∀ n, σ n < σ (n + 1) ∧ a (σ n) < a (σ (n + 1)) := by
    intro n
    induction n with
    | zero =>
      have _h1 : f (K + 1) > K + 1 := by bound
      have _h2 : a (f (K + 1)) > a (K + 1) := by bound
      have _h3 : σ 0 = K + 1 := by bound
      have _h4 : σ 1 = f (K + 1) := by bound
      bound
    | succ n hn =>
      have _h1 : σ (n + 1) < σ (n + 1 + 1) := by
        calc
          σ (n + 1 + 1) = f^[n + 1 + 1] (K + 1) := by bound
          _ = f (f^[n+1] (K + 1)) := by rewrite[Function.iterate_succ_apply'];rfl
          _ = f (σ (n + 1)) := by rewrite[Function.iterate_succ_apply];rfl
          _ > σ (n + 1) := by bound
      have _h2 : a (σ (n + 1)) < a (σ (n + 1 + 1)) := by
        calc
          a (σ (n + 1 + 1)) = a (f^[n + 1 + 1] (K + 1)) := by bound
          _ = a (f (f^[n+1] (K + 1))) := by rewrite[Function.iterate_succ_apply'];rfl
          _ = a (f (σ (n + 1))):= by rewrite[Function.iterate_succ_apply];rfl
          _ > a (σ (n + 1)) := by bound
      exact ⟨_h1, _h2⟩
  use σ
  split_ands
  · apply subseq_of_succ
    intro n
    apply (hr n).left
  · change ∀ ⦃i j⦄, i ≤ j → (a ∘ σ) i ≤ (a ∘ σ) j
    have _h : ∀ m k, (a ∘ σ) m ≤ (a ∘ σ) (m + k) := by
      intro m k
      induction k with
      | zero => norm_num;
      | succ k hk =>
        have _h : (a ∘ σ) m < (a ∘ σ) (m + (k + 1)) := by
          calc
            (a ∘ σ) m ≤ (a ∘ σ) (m + k) := by bound
            _ = a (σ (m + k)) := by bound
            _ < a (σ (m + k + 1)) := by apply (hr (m + k)).right
            _ = (a ∘ σ) (m + (k + 1)) := by bound
        bound
    intro i j hij
    specialize _h i (j - i)
    have _h2 : j = i + (j - i) := by omega
    rewrite[_h2]
    apply _h
