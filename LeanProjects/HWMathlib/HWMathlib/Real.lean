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

def IsCauchy {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) : Prop := ∀ (ε : X), 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n, |a m - a n| < ε

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
    _ = |a m - L| + |a n - L| := by nth_rewrite 2 [abs_sub_comm];rfl
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
  apply strictMono_nat_of_lt_succ hσ
--   intro i j h
--   have _h1 : ∀ k m : ℕ, σ k < σ (k +(m + 1)) := by
--     intro k m
--     induction m with
--     |zero =>
--       bound
--     |succ m hm =>
--       calc
--         σ (k + (m + 1 + 1)) = σ (k + m + 1 + 1) := by bound
--         _ > σ (k + m + 1) := by bound
--         _ > σ (k) := by bound
-- -- TODO 又多了一个omega，不知道omega, bound, linarith, norm_num, field_simp, simp之间的区别
--   have _h2 : j = i + ((j - i - 1) + 1) := by omega
--   rewrite[_h2]
--   apply _h1 i (j - i - 1)

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
  have hσ0 : σ 0 = K + 1 := by bound
  have hσsucc : ∀ k, σ (k + 1) = f (σ k) := by
    intro k
    calc
      σ (k + 1) = f^[k+1] (K + 1) := by bound
      _ = f (f^[k] (K + 1)) := by rewrite[Function.iterate_succ_apply'];rfl
      _ = f (σ k) := by bound
  have hσ : ∀ n, σ n > K := by
    intro n
    induction n with
    | zero => rewrite[hσ0];bound
    | succ n hn =>
      rewrite[hσsucc n]
      have := hf1 (σ n) hn
      bound

  have hr1 : ∀ n, σ n < σ (n + 1) := by
    intro n
    rewrite[hσsucc n]
    apply hf1 (σ n) (hσ n)

  have hr2 : ∀ n, a (σ n) < a (σ (n + 1)) := by
    intro n
    rewrite[hσsucc n]
    apply hf2 (σ n) (hσ n)

  use σ
  split_ands
  · apply subseq_of_succ
    intro n
    apply hr1 n
  · apply monotone_nat_of_le_succ
    intro k
    apply le_of_lt (hr2 k)
    -- change ∀ ⦃i j⦄, i ≤ j → (a ∘ σ) i ≤ (a ∘ σ) j
    -- have _h : ∀ m k, (a ∘ σ) m ≤ (a ∘ σ) (m + k) := by
    --   intro m k
    --   induction k with
    --   | zero => norm_num;
    --   | succ k hk =>
    --     have _h : (a ∘ σ) m < (a ∘ σ) (m + (k + 1)) := by
    --       calc
    --         (a ∘ σ) m ≤ (a ∘ σ) (m + k) := by bound
    --         _ = a (σ (m + k)) := by bound
    --         _ < a (σ (m + k + 1)) := by apply hr2 (m + k)
    --         _ = (a ∘ σ) (m + (k + 1)) := by bound
    --     bound
    -- intro i j hij
    -- specialize _h i (j - i)
    -- have _h2 : j = i + (j - i) := by omega
    -- rewrite[_h2]
    -- apply _h

theorem MonotoneNeg_of_Antitone {X} [LinearOrder X] [AddCommGroup X] [IsOrderedAddMonoid X] (a : ℕ → X) (ha : Antitone a) : Monotone (-a) := by
  unfold Monotone
  unfold Antitone at ha
  intro i j hij
  have := ha hij
  calc
    (-a) i = - (a i) := by bound
    _ ≤  - (a j) := by bound
    _ = (-a) j := by bound

theorem IsCauchyNeg {X} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] (a : ℕ → X) (ha : IsCauchy a) : IsCauchy (-a) := by
  unfold IsCauchy
  intro ε hε
  unfold IsCauchy at ha
  rcases ha ε hε with ⟨N, hN⟩
  use N
  intro n hn m hm
  rcases hN n hn m hm with hmn
  calc
    |(-a) m - (-a) n| = |- a m + a n| := by bound
    _ = |-(a m - a n)| := by ring_nf
    _ = |a m - a n| := by apply abs_neg
    _ < ε := by bound


theorem IsCauchy_of_AntitoneBdd {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] {a : ℕ → X} {M : X} (ha : Antitone a) (hM : ∀ n, M ≤ a n) : IsCauchy a := by
  let b : ℕ → X := fun n => - (a n)
  have hba : -b = a := by
    funext n
    change -(-(a n)) = a n
    bound
  have hb : Monotone b := MonotoneNeg_of_Antitone a ha
  have hbM : ∀ n, - M ≥ b n := by
    intro n
    bound
  have hbCauchy := IsCauchy_of_MonotoneBdd hb hbM
  have r := IsCauchyNeg b hbCauchy
  rewrite[hba] at r
  apply r

example (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / n) : IsCauchy a ∧ ¬ Monotone a ∧ ¬ Antitone a := by
  split_ands
  · unfold IsCauchy
    intro ε hε
    have hε2 : ε/2 > 0 := by bound
    rcases ArchProp hε2 with ⟨N, hN⟩
    have hεgt0 : 1/(ε/2) > 0 := by field_simp; bound
    have hNgt0 : (N:ℝ) > 0 := by linarith
    field_simp at hN
    have _h1 : 1/N < ε/2 := by field_simp; bound
    use (N + 1)
    intro n hn m hm
    have _hngeNp1 : (n:ℝ) ≥ (N:ℝ) + 1 := by exact_mod_cast hn
    have _hngtN : (n:ℝ) > (N:ℝ) := by bound
    have _hngeM : (m:ℝ) ≥ (n:ℝ) := by exact_mod_cast hm
    have _hngt0 : (n:ℝ) > 0 := by bound
    have _hmgt0 : (m:ℝ) > 0 := by bound
    have _h2 : 1/(n:ℝ) < 1/(N:ℝ) := by field_simp; bound
    have _h3 : 1/(m:ℝ) < 1/(N:ℝ) := by field_simp; bound
    calc
      |a m - a n| ≤ |a m| + |a n| := by apply abs_sub
      _ = |1/(m:ℝ)| + |1/(n:ℝ)| := by rewrite[ha m, ha n];rfl
      _ = 1/(m:ℝ) + 1/(n:ℝ) := by bound
      _ < ε/2 + ε/2 := by bound
      _ = ε := by bound
  · intro hmono
-- 这里对hmono要传入的参数是 (1 ≤ 2)，直接写 by bound 就可以了，爽
    have h12 : a 1 ≤ a 2 := hmono (by bound)
    rw[ha 1, ha 2] at h12
    bound
  · intro hanti
    have h01 : a 1 ≤ a 0 := hanti (by bound)
    rw [ha 0, ha 1] at h01
-- 我是没想到 1/1 ≤ 1/0 居然是False
    bound

theorem AntitoneSubseq_of_UnBddPeaks {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : UnBddPeaks a) : ∃ σ, Subseq σ ∧ Antitone (a ∘ σ) := by
  unfold UnBddPeaks at ha
  choose f hf1 hf2 using ha
/-！
Nat.rec接收三个参数
第一个参数：当 k = 0 时
第二个参数：也是一个fun，接收两个参数（当前的k，上一步归纳的结果即 σ k）
第三个参数：k对应的自然数

效果与 σ1, σ2, σ3 等价
--/
  let σ : ℕ → ℕ := fun n => Nat.rec (f 1) (fun _ σk => f σk) n
  -- let σ1 : ℕ → ℕ := fun n => n.rec (f 1) (fun _ σk => f σk)
  -- let σ2 : ℕ → ℕ | 0 => f 1 | k+1 => f (σ2 k) 这里 σ2 只是局部的，所以σ2 k的调用不成立，需要 σ2 用def定义成全局的才行，但这就又要求 f 也是全局的了
  -- let σ3 : ℕ → ℕ := fun n => f^[n] 1
-- 之所以选择 Nat.rec 的递归描述，就是为了下面得到 hσ0 和 hσsucc 很简单
-- 因为这里使用了Lean内置的归约规则
-- Nat.rec z s 0 = z，也即
-- σ 0 = Nat.rec (f 1) (fun _ σk => f σk) 0 = f 1
-- Nat.rec z s (k+1) = s k (Nat.rec z s k)，也即
-- σ (n + 1) = Nat.rec (f 1) (fun _ σk => f σk) (n + 1) = (fun _ σk => f σk) n (σ n)
-- 中间过程的理解可以省略，直接认为
-- σ (n + 1) = (fun _ σk => f σk) n (σ n)
-- 这其实就是一个函数 (fun _ σk => f σk) ，然后传入两个参数 n 和 (σ n) ，得到函数执行的结果，也就是
-- f (σ n)
  have hσ0 : σ 0 = f 1 := rfl
  have hσsucc : ∀ n, σ (n + 1) = f (σ n) := fun n => rfl
-- 也可以写成下面两种形式
  -- have hσsucc : ∀ n, σ (n + 1) = f (σ n) := by intro n;rfl
  -- have hσsucc n: σ (n + 1) = f (σ n) := rfl
  have hmono : ∀ n, σ n < σ (n + 1) := by
    intro n
    rewrite[hσsucc n]
    apply hf1
  have hPeak : ∀ n, IsAPeak a (σ n) := by
    intro n
    induction n with
    | zero =>
      rewrite[hσ0]
      apply hf2
    | succ n _ =>
      rewrite[hσsucc n]
      apply hf2
  have hAnti : ∀ n, a (σ (n + 1)) ≤ a (σ n) := by
    intro n
    apply hPeak
    apply hmono

  use σ
  split_ands
  · apply strictMono_nat_of_lt_succ
    apply hmono
  · apply antitone_nat_of_succ_le
    apply hAnti

theorem BolzanoWeierstrass {X : Type*} [NormedField X] [LinearOrder X] [IsStrictOrderedRing X] [FloorSemiring X] (a : ℕ → X) (ha : SeqBdd a) : ∃ σ, Subseq σ ∧ IsCauchy (a ∘ σ) := by
  rcases ha with ⟨M, ⟨hM1, hM2⟩⟩
  by_cases h : UnBddPeaks a
  · rcases AntitoneSubseq_of_UnBddPeaks a h with ⟨σ, ⟨hσ1, hσ2⟩⟩
    use σ
    split_ands
    · apply hσ1
    · have _h : ∀ n, -M ≤ (a ∘ σ) n := by
        intro n
        specialize hM2 (σ n)
        rewrite[abs_le] at hM2
        apply hM2.left
      apply IsCauchy_of_AntitoneBdd hσ2 _h
  · rcases MonotoneSubseq_of_BddPeaks a h with ⟨σ, ⟨hσ1, hσ2⟩⟩
    use σ
    split_ands
    · apply hσ1
    · have _h : ∀ n, M ≥ (a ∘ σ) n := by
        intro n
        specialize hM2 (σ n)
        rewrite[abs_le] at hM2
        apply hM2.right
      apply IsCauchy_of_MonotoneBdd hσ2 _h

/-
IsCauSeq abs a，根据定义，展开后就是
∀ε > 0, ∃i, ∀j ≥ i, |a j - a i| < ε
-/
theorem IsCauSeq_of_IsCauchy {a : ℕ → ℚ} (ha : IsCauchy a) : IsCauSeq abs a := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  -- use N
  -- intro j hj
  -- exact hN N (le_refl N) j hj
  exact ⟨N, fun j hj => hN N (le_refl N) j hj⟩

def Real_of_CauSeq {a : ℕ → ℚ} (ha : IsCauchy a) : ℝ := Real.mk ⟨a, IsCauSeq_of_IsCauchy ha⟩

theorem SeqLim_of_Real_of_Cau {a : ℕ → ℚ} (ha : IsCauchy a) : SeqLim (fun x => ↑(a x)) (Real_of_CauSeq ha) := by
  intro ε hε
  -- 不能直接用 ε/2 ，因为 ha 接收的参数需要是一个有理数，不能是实数
  rcases exists_rat_btwn (show 0 < ε/2 by bound) with ⟨δ, hδ0, hδε⟩
  have hδpos : (0:ℚ) < δ := by exact_mod_cast hδ0
  rcases ha δ hδpos with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have key : |Real_of_CauSeq ha - (a n : ℝ)| ≤ (2 * (δ:ℝ)) := by
    apply Real.mk_near_of_forall_near
    refine ⟨N, fun j hj => ?_⟩
    have h1 : |a j - a N| < δ := hN N (by bound) j hj
    have h2 : |a n - a N| < δ := hN N (by bound) n hn
    have h3 : |a j - a n| < 2 * δ := by
      calc
        |a j - a n| = |a j - a N - (a n - a N)| := by bound
        _ ≤ |a j - a N| + |a n - a N| := by apply abs_sub
        _ < δ + δ := by bound
        _ = 2 * δ := by bound
    have hcast : |(a j : ℝ) - (a n : ℝ)| = |a j - a n| := by bound
    rewrite[hcast]
    exact_mod_cast h3.le
  rewrite[abs_sub_comm] at key
  have h : 2 * (δ : ℝ) < ε := by bound
  bound

theorem Reals_are_Complete (q : ℕ → ℕ → ℚ) (x : ℕ → ℝ) (hq : ∀ n, IsCauchy (q n)) (hx : ∀ n, x n = Real_of_CauSeq (hq n)) (hxCau : IsCauchy x) : ∃ (y : ℕ → ℚ) (hy : IsCauchy y), SeqLim x (Real_of_CauSeq hy) := by
  -- 核心思路：要构建数列 y n -> x，两步走
  ---- 先构建 y n -> x n
  ---- 再由 x n -> x
  -- 每个q n都是一个数列，都收敛到x n
  -- 因为q n 是 ℕ → ℚ，但SeqLim的第一个参数应该是 ℕ → ℝ，所以通过 fun m => ((q n m) : ℝ)做一下转换
  have hconv : ∀ n, SeqLim (fun m => (q n m : ℝ)) (x n) := by
    intro n
    rewrite[hx n]
    apply SeqLim_of_Real_of_Cau (hq n)
  have hk : ∀ n, ∃ k, ∀ m ≥ k, |(q n m : ℝ) - (x n)| < 1/(n+1) := by
    intro n
    rcases hconv n (1/(n+1)) (by positivity) with ⟨N, hN⟩
    exact ⟨N, hN⟩
  choose k hk using hk
  -- 至此，数列 y 就已经构建好了，下面就是证明 y n -> x
  -- 根据结论的需要，下面就是证明 y 是 Cauchy 列
  -- 最后再证明 SeqLim x (Real_of_CauSeq hy)
  let y : ℕ → ℚ := fun n => q n (k n)
  have hyCau : IsCauchy y := by
    intro ε hε
    have hε3pos : 0 < ((ε/3):ℝ) := by positivity
    rcases hxCau (ε/3) hε3pos with ⟨N1, hN1⟩
    rcases exists_nat_one_div_lt hε3pos with ⟨N2, hN2⟩
    refine ⟨N1 + N2, fun n hn m hm => ?_⟩

    -- 如果直接写1/(N2+1)，field_simp 就不会产生效果，因为自然数不是域，没有field_simp能使用的逆元结构，所以如果要用field_simp必须先强调转成 ℝ
    -- gcongr 比 field_simp 好用多了
    have hmε : 1/(m+1) ≤ 1/((N2:ℝ) + 1) := by gcongr;bound
    have hnε : 1/(n+1) ≤ 1/((N2:ℝ) + 1) := by gcongr;bound

    have h1 : |y m - x m| < ε/3 := by
      have _h1 : |y m - x m| < 1/(m+1) := hk m (k m) (by bound)
      bound
    have h2 : |x n - y n| < ε/3 := by
      have _h1 : |y n - x n| < 1/(n+1) := hk n (k n) (by bound)
      rewrite[abs_sub_comm]
      bound
    have h3 : |x m - x n| < ε/3 := hN1 n (by bound) m hm

    have r1 : |((y m):ℝ) - ((y n):ℝ)| ≤ |y m - x m| + |x m - y n| := by apply abs_sub_le ((y m):ℝ) (x m) ((y n):ℝ)
    have r2 : |x m - ((y n):ℝ)| ≤ |x m - x n| + |x n - y n| := by apply abs_sub_le (x m) (x n) ((y n):ℝ)
    have hε : (|y m - y n| : ℝ) < (ε : ℝ) := by
      calc
        (|y m - y n| : ℝ) = |((y m):ℝ) - ((y n):ℝ)| := by bound
        _ ≤ |y m - x m| + |x m - x n| + |x n - y n| := by bound
        _ < ε/3 + ε/3 + ε/3 := by bound
        _ = ε := by bound
    exact_mod_cast hε

  refine ⟨y, hyCau, ?_⟩

  -- 最后证明 SeqLim x (Real_of_CauSeq hyCau)
  -- 根据 SeqLim_of_Real_of_Cau ，我们知道 y n 的极限是 (Real_of_CauSeq hyCau)
  -- 再结合 y n 的极限是 x n
  -- 那么通过三角不等式就能证明 x n 的极限也是 (Real_of_CauSeq hyCau)

  have hyconv : SeqLim (fun n => y n) (Real_of_CauSeq hyCau) := by
    apply SeqLim_of_Real_of_Cau hyCau
  intro ε hε
  have hε2pos : 0 < ((ε/2):ℝ) := by positivity
  rcases hyconv (ε/2) hε2pos with ⟨N1, hN1⟩
  rcases exists_nat_one_div_lt hε2pos with ⟨N2, hN2⟩
  refine ⟨N1 + N2, fun n hn => ?_⟩

  have h1 : |y n - Real_of_CauSeq hyCau| < ε/2 := hN1 n (by bound)
  have h2 : |x n - y n| < ε/2 := by
    rewrite[abs_sub_comm]
    have _h1 := hk n (k n) (by bound)
    have _h2 : 1/((n:ℝ)+1) ≤ 1/((N2:ℝ)+1) := by field_simp; gcongr;bound
    bound
  calc
    |x n - Real_of_CauSeq hyCau| ≤ |x n - y n| + |y n - Real_of_CauSeq hyCau| := by apply abs_sub_le (x n) (y n) (Real_of_CauSeq hyCau)
    _ < ε/2 + ε/2 := by bound
    _ = ε := by bound

example (a b : ℕ → ℚ) (ha : ∀ n, a n = 1 - 1 / 2 ^ n) (hb : ∀ n, b n = 1) : ∀ ε > 0, ∃ N, ∀ n ≥ N, |a n - b n| < ε := by
  intro ε hε
  have _hε : (0:ℝ) < (ε:ℝ) := by exact_mod_cast hε
  rcases ArchProp _hε with ⟨N, hN⟩

  refine ⟨N + 1, fun n hn => ?_⟩

  have h1ε : 1/ (ε:ℝ) > 0 := by bound
  have hNpos : N > 0 := by
    have _hNpos : (N:ℝ) > 0 := by linarith
    exact_mod_cast _hNpos
  have hnN : n > N := by bound
  have hnpos : n > 0 := by bound

  calc
    |a n - b n| = |(1 - 1/2^n) - 1| := by rewrite[ha n, hb n];rfl
    _ = |-(1/2^n)| := by ring_nf
    _ = |1/2^n| := by apply abs_neg
    _ = 1/2^n := by bound
    _ < 1/(n:ℚ) := by
      have _h1 : n < 2^n := by apply IdLeTwoPow
      field_simp
      exact_mod_cast _h1
    _ < 1/(N:ℚ) := by field_simp; exact_mod_cast hnN
    _ < ε := by
      field_simp
      field_simp at hN
      rewrite[mul_comm]
      exact_mod_cast hN


def Series (a : ℕ → ℝ) : ℕ → ℝ := fun n ↦ ∑ k ∈ range n, a k
def SeriesConv (a : ℕ → ℝ) : Prop := SeqConv (Series a)
def SeriesLim (a : ℕ → ℝ) (L : ℝ) : Prop := SeqLim (Series a) L

theorem LimZero_of_SeriesConv (a : ℕ → ℝ) (ha : SeriesConv a) : SeqLim a 0 := by
  intro ε hε
  rcases ha with ⟨L, hL⟩
  rcases hL (ε/2) (by bound) with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  have hstep : a n = Series a (n+1) - Series a n := by
    unfold Series
    rewrite[sum_range_succ]
    bound
  rewrite[hstep, sub_zero]

  have h1 : |Series a (n+1) - L| < ε/2 := hN (n+1) (by bound)
  have h2 : |Series a n - L| < ε/2 := hN n (by bound)
  rewrite[abs_sub_comm] at h2

  calc
    |Series a (n+1) - Series a n| ≤ |Series a (n+1) - L| + |L - Series a n| := by apply abs_sub_le
    _ < ε/2 + ε/2 := by bound
    _ = ε := by bound
  -- unfold SeqLim
  -- by_contra h
  -- push Not at h
  -- rcases h with ⟨ε, hε, hN⟩
  -- choose σ hσ using hN
  -- unfold SeriesConv SeqConv Series SeqLim at ha
  -- rcases ha with ⟨L, hL⟩
  -- rcases hL (ε/2) (by bound) with ⟨N, hN⟩

  -- have hc := hσ N
  -- have hcl := hc.left
  -- have hcr := hc.right
  -- have _h1 := hN (σ N) (by bound)
  -- have _h2 := hN (σ N + 1) (by bound)
  -- rewrite[abs_sub_comm] at _h1

  -- have key : a (σ N) = ∑ k ∈ range (σ N + 1), a k - ∑ k ∈ range (σ N), a k := by
  --   rewrite[sum_range_succ]
  --   bound

  -- have hx : |a (σ N)| < ε := by
  --   calc
  --     |a (σ N)| = |∑ k ∈ range (σ N + 1), a k - ∑ k ∈ range (σ N), a k| := by rewrite[key];rfl
  --     _ ≤ |(∑ k ∈ range (σ N + 1), a k) - L| + |L - (∑ k ∈ range (σ N), a k)| := by apply abs_sub_le
  --     _ < ε/2 + ε/2 := by bound
  --     _ = ε := by bound
  -- rewrite[sub_zero] at hcr
  -- bound

theorem FiniteGeomSeries (x : ℝ) (n : ℕ) : (1 - x) * ∑ k ∈ range n, x ^ k = 1 - x ^ n := by
  induction n with
  | zero => bound
  | succ n hn =>
    rewrite[sum_range_succ]
    rewrite[mul_add]
    rewrite[hn]
    calc
      1 - x^n + (1-x)*x^n = 1 - x^n + (x^n - x^(n+1)) := by ring_nf
      _ = 1 - x^(n+1) := by norm_num

theorem SeriesConstMul (a b : ℕ → ℝ) (c : ℝ) (hb : ∀ n, b n = c * a n) : ∀ n, Series b n = c * Series a n := by
  intro n
  unfold Series
  induction n with
  | zero => bound
  | succ n hn =>
  rewrite[sum_range_succ]
  rewrite[sum_range_succ]
  rewrite[hn]
  ring_nf
  rewrite[hb n]
  bound

theorem SeriesAdd (a b c : ℕ → ℝ) (h : ∀ n, c n = a n + b n) : ∀ n, Series c n = Series a n + Series b n := by
  intro n
  unfold Series
  induction n with
  | zero => bound
  | succ n hn =>
  rewrite[sum_range_succ]
  rewrite[sum_range_succ]
  rewrite[sum_range_succ]
  rewrite[hn]
  rewrite[h n]
  bound

theorem LeibnizSeriesFinite {a : ℕ → ℝ} (ha : ∀ n, a n = 1 / ((n + 1) * (n + 2))) : ∀ n, ∑ k ∈ range n, a k = 1 - 1 / (n + 1) := by
  intro n
  induction n with
  | zero => bound
  | succ n hn =>
  rewrite[sum_range_succ, hn, ha]
  field_simp
  ring_nf
  norm_num
  bound

theorem LeibnizSeries (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / ((n + 1) * (n + 2))) : SeriesConv a := by
  use 1
  intro ε hε
  rcases ArchProp hε with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩

  have h1 : n + 1 > N := by bound
  have h2 : n + 1 > (N:ℝ) := by exact_mod_cast h1
  have hNpos : (N:ℝ) > 0 := by
    have h1εpos : 1/ε > 0 := by field_simp;bound
    linarith
  have h3 : 1/(n+1) < 1/(N:ℝ) := by bound
  have h4 : 1/(N:ℝ) < ε := by
    field_simp
    field_simp at hN
    rewrite[mul_comm]
    apply hN
  have h5 : 1/(n+1) < (ε:ℝ) := by bound

  unfold Series
  rewrite[LeibnizSeriesFinite ha n]
  calc
    |1 - 1/((n:ℝ)+1) - 1| = |-(1/((n:ℝ) + 1))| := by ring_nf
    _ = |1/((n:ℝ) + 1)| := by apply abs_neg
    _ = 1/((n:ℝ) + 1) := by
      apply abs_of_nonneg
      field_simp
      linarith
    _ < ε := by bound

theorem SeriesOrderThm {a b : ℕ → ℝ} (hab : ∀ n, a n ≤ b n) : ∀ n, Series a n ≤ Series b n := by
  intro n
  induction n with
  | zero => bound
  | succ n hn =>
    unfold Series at hn
    unfold Series
    rewrite[sum_range_succ]
    rewrite[sum_range_succ]
    specialize hab n
    linarith

-- TODO 没我想像的那么简单么，后面再梳理一下吧，不借用Mathlib里面的CauchySeq，自己证一遍吧
theorem SeqConv_of_IsCauchy (a : ℕ → ℝ) (ha : IsCauchy a) : SeqConv a := by
  have hCS : CauchySeq a := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := ha ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [Real.dist_eq]
    rcases le_total n m with h | h
    · exact hN n hn m h
    · rw [abs_sub_comm]; exact hN m hm n h
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hCS
  refine ⟨L, fun ε hε => ?_⟩
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hL ε hε
  exact ⟨N, fun n hn => by have := hN n hn; rwa [Real.dist_eq] at this⟩

theorem SeqConv_of_MonotoneBdd (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, a n ≤ M) (ha : Monotone a) : SeqConv a := by
  exact SeqConv_of_IsCauchy a (IsCauchy_of_MonotoneBdd ha hM)

theorem SeqConv_of_AntitoneBdd (a : ℕ → ℝ) (M : ℝ) (hM : ∀ n, a n ≥ M) (ha : Antitone a) : SeqConv a := by
  exact SeqConv_of_IsCauchy a (IsCauchy_of_AntitoneBdd ha hM)

example (a : ℕ → ℝ) (ha : ∀ n, a n = 1 / ((n + 2) ^ 2)) : SeriesConv a := by
  let b : ℕ → ℝ := fun n ↦ 1/((n+1)*(n+2))
  have hb : ∀ n, b n = 1/((n+1)*(n+2)) := by bound
  have hab : ∀ n, a n ≤ b n := by
    intro n
    rewrite[ha n, hb n]
    field_simp
    bound

  have habb : ∀ n, Series a n ≤ 1 := by
    intro n
    have _h1 := SeriesOrderThm hab n
    have _h2 : Series b n ≤ 1 := by
      unfold Series
      rewrite[LeibnizSeriesFinite hb n]
      norm_num
      bound
    bound
  have hmono : Monotone (Series a) := by
    apply monotone_nat_of_le_succ
    intro n
    unfold Series
    rewrite[sum_range_succ]
    have hanpos : a n > 0 := by
      rewrite[ha n]
      bound
    bound
  apply SeqConv_of_MonotoneBdd (Series a) (1) habb hmono

def AbsSeriesConv (a : ℕ → ℝ) := SeriesConv (fun n ↦ |a n|)

theorem DiffOfSeries (a : ℕ → ℝ) {n m} (hmn : n ≤ m) : Series a m - Series a n = ∑ k ∈ Finset.Ico n m, a k := by
  have hr : ∀d : ℕ, Series a (n + d) - Series a n = ∑ k ∈ Ico n (n+d), a k := by
    intro d
    induction d with
    | zero =>  bound
    | succ d hd =>
    rewrite[← add_assoc]
    rewrite[sum_Ico_succ_top (show n ≤ (n + d) by bound) a]
    rewrite[← hd]
    unfold Series
    rewrite[sum_range_succ]
    bound
  have h := hr (m - n)
  rewrite[show n+(m-n)=m by omega] at h
  bound

theorem Series_abs_add (a : ℕ → ℝ) {n m} (hmn : n ≤ m) : |∑ k ∈ Finset.Ico n m, a k| ≤ ∑ k ∈ Finset.Ico n m, |a k| := by
  have hr : ∀d : ℕ,  |∑ k ∈ Ico n (n+d), a k| ≤ ∑ k ∈ Ico n (n+d), |a k| := by
    intro d
    induction d with
    | zero => bound
    | succ d hd =>
    rewrite[← add_assoc]
    rewrite[sum_Ico_succ_top (show  n ≤ n+d by bound) a]
    rewrite[sum_Ico_succ_top (show  n ≤ n+d by bound) (fun k => |a k|)]
    have _h1 : |∑ k ∈ Ico n (n+d), a k + a (n+d)| ≤ |∑ k ∈ Ico n (n+d), a k| + |a (n+d)| := by apply abs_add_le
    have _h2 : |∑ k ∈ Ico n (n+d), a k + a (n+d)| ≤ ∑ k ∈ Ico  n (n+d), |a k| + |a (n+d)| := by bound
    bound

  have h := hr (m - n)
  rewrite[show n+(m-n)=m by omega] at h
  bound

theorem Conv_of_AbsSeriesConv {a : ℕ → ℝ} (ha : AbsSeriesConv a) : SeriesConv a := by
  unfold AbsSeriesConv SeriesConv at ha
  have h := IsCauchy_of_SeqConv ha
  have hr : IsCauchy (Series a) := by
    intro ε hε
    rcases h ε hε with ⟨N, hN⟩
    refine ⟨N, fun n hn m hm => ?_⟩
    rewrite[DiffOfSeries a hm]
    have habs:= hN n hn m hm

    rewrite[DiffOfSeries (fun n => |a n|) hm] at habs

    have hr1 : |∑ k ∈ Ico n m, a k| ≤ ∑ k ∈ Ico n m, |a k| := by apply Series_abs_add a hm
    have hr2 : ∑ k ∈ Ico n m, |a k| ≤ |(∑ k ∈ Ico n m, |a k|)| := by bound
    bound
  exact SeqConv_of_IsCauchy (Series a) hr

theorem AntitoneLimitBound {a} (ha : Antitone a) {L} (aLim : SeqLim a L) (n : ℕ) : L ≤ a n := by
  by_contra hc
  push Not at hc
  let ε := L - a n
  rcases aLim ε (by bound) with ⟨N, hN⟩
  have hdiff1 := hN (n + N) (by bound)
  rewrite[abs_lt] at hdiff1
  have hdiff2 := ha (show n ≤ n + N by bound)
  have hdiff3 : a n = L - ε := by bound
  bound

theorem CoherenceOfReals {a b} {L M} (ha : SeqLim a L) (hb : SeqLim b M) (hab : SeqLim (fun n => a n - b n) 0) : L = M := by
  by_contra hc
  let ε := |L-M|
  have hε : ε > 0 := by
    have hpos : |L - M| > 0 := by apply abs_pos.mpr (by bound)
    bound
  rcases ha (ε/4) (by bound) with ⟨Na, hNa⟩
  rcases hb (ε/4) (by bound) with ⟨Nb, hNb⟩
  rcases hab (ε/4) (by bound) with ⟨Nab, hNab⟩

  let Max := Na + Nb + Nab
  have vM : Max = Na + Nb + Nab := by bound

  have hamax := hNa Max (by bound)
  have hbmax := hNb Max (by bound)
  have hab := hNab Max (by bound)
  norm_num at hab

  have htri : |L - M| ≤ |L - a Max| + |a Max - b Max| + |b Max - M| := by
    have : |L - M| ≤ |L - a Max| + |a Max - M| := by apply abs_sub_le
    have : |a Max - M| ≤ |a Max - b Max| + |b Max - M| := by apply abs_sub_le
    bound

  rewrite[abs_sub_comm] at hamax
  have : |L - M| ≤ 3*ε/4 := by bound
  bound


theorem SeqEvenOdd {a} {L} (ha2n : SeqLim (fun n => a (2 * n)) L) (ha2np1 : SeqLim (fun n => a (2 * n + 1)) L) : SeqLim a L := by
  intro ε hε
  rcases ha2n ε hε with ⟨Ne, hNe⟩
  rcases ha2np1 ε hε with ⟨No, hNo⟩

  refine ⟨(2 * Ne) + (2 * No + 1), fun n hn => ?_⟩
-- TODO 对自然数 n 分奇偶讨论
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · have hkNe : k ≥ Ne := by bound
    have hn2k : n = 2*k := by bound
    rewrite[hn2k]
    exact hNe k hkNe
  · have hkNo : k ≥ No := by bound
    rewrite[hk]
    exact hNo k hkNo

theorem AntitoneSeriesOdd {a : ℕ → ℝ} (ha : Antitone a) (_ : ∀ n, 0 ≤ a n) : Antitone fun n => ∑ k ∈ Finset.range (2 * n + 1), (-1) ^ k * a k := by
  apply antitone_nat_of_succ_le
  intro n
  rewrite[sum_range_succ]
  nth_rewrite 1 [show 2*(n+1) = 2*n+1+1 by omega]
  rewrite[sum_range_succ]
-- 这里 hodd 和 heven 的证明可以这么简洁，同时又略有不同，其实只要unfold Odd和Even就能理解了
  have hodd : Odd (2 * n + 1) := ⟨n, rfl⟩
  have heven : Even (2 * (n+1)) := ⟨n+1, by bound⟩
  rewrite[Odd.neg_one_pow hodd, Even.neg_one_pow heven]
  have hmono : a (2*(n+1)) ≤ a (2*n+1) := by bound
  bound

theorem BddSeriesEven {a : ℕ → ℝ} (ha : Antitone a) (apos : ∀ n, 0 ≤ a n) (n : ℕ) : ∑ k ∈ Finset.range (2 * n), (-1) ^ k * a k ≤ a 0 := by
  have hstep : ∑ k ∈ Finset.range (2 * n), (-1) ^ k * a k
      ≤ ∑ k ∈ Finset.range (2 * n + 1), (-1) ^ k * a k := by
    rw [Finset.sum_range_succ]
    have heven : Even (2 * n) := ⟨n, by ring⟩
    have h2n : (0:ℝ) ≤ (-1) ^ (2 * n) * a (2 * n) := by
      rw [Even.neg_one_pow heven]
      bound
    bound
  have hodd : ∑ k ∈ Finset.range (2 * n + 1), (-1) ^ k * a k
      ≤ ∑ k ∈ Finset.range (2 * 0 + 1), (-1) ^ k * a k :=
    (AntitoneSeriesOdd ha apos) (by bound)
  simp at hodd
  bound

theorem BddSeriesOdd {a : ℕ → ℝ} (ha : Antitone a) (apos : ∀ n, 0 ≤ a n) (n : ℕ) : 0 ≤ ∑ k ∈ Finset.range (2 * n + 1), (-1) ^ k * a k := by
  have h2n : 0 ≤ ∑ k ∈ range (2*n), (-1)^k * a k := by
    induction n with
    | zero => bound
    | succ n hn =>
    rewrite[show 2*(n+1)=2*n+1+1 by bound, sum_range_succ, sum_range_succ]
    have heven : Even (2*n) := ⟨n, by bound⟩
    have hodd : Odd (2*n+1) := ⟨n, rfl⟩
    rewrite[Even.neg_one_pow heven, Odd.neg_one_pow hodd]

    have _h1 : a (2*n) ≥ a (2*n+1) := ha (show 2*n ≤ 2*n+1 by bound)
    have _h2 : 1*a (2*n) - (-1)*a (2*n+1) ≥ 0 := by bound
    linarith
  rewrite[sum_range_succ]
  have heven : Even (2*n) := ⟨n, by bound⟩
  rewrite[Even.neg_one_pow heven]
  bound

theorem DiffGoesToZero {a} (aLim : SeqLim a 0) : SeqLim (fun n => ∑ k ∈ Finset.range (2 * n + 1), (-1) ^ k * a k - ∑ k ∈ Finset.range (2 * n), (-1) ^ k * a k) 0 := by
  have hd : ∀ n, ∑ k ∈ Finset.range (2 * n + 1), (-1) ^ k * a k - ∑ k ∈ Finset.range (2 * n), (-1) ^ k * a k = (-1)^(2*n)* a (2*n) := by
    intro n
    rewrite[sum_range_succ]
    bound
  intro ε hε
  rcases aLim ε hε with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  norm_num
  rewrite[hd n]
  norm_num
  have _h1 : 2*n ≥ N := by bound
  have _h2 := hN (2*n) (by bound)
  norm_num at _h2
  exact _h2

theorem MonotoneSeriesEven {a : ℕ → ℝ} (ha : Antitone a) (_ : ∀ n, 0 ≤ a n) : Monotone fun n => ∑ k ∈ Finset.range (2 * n), (-1) ^ k * a k := by
  apply monotone_nat_of_le_succ
  intro n
  rewrite[show 2*(n+1) = 2*n+1+1 by omega]
  rewrite[sum_range_succ, sum_range_succ]
  have heven : Even (2*n) := ⟨n, by bound⟩
  have hodd : Odd (2*n+1) := ⟨n, rfl⟩
  rewrite[Odd.neg_one_pow hodd, Even.neg_one_pow heven]
  have hanti : a (2*n+1) ≤ a (2*n) := by bound
  bound

theorem AlternatingSeriesTest {a : ℕ → ℝ} (ha : Antitone a) (aLim : SeqLim a 0) : SeriesConv (fun n ↦ (-1)^n * a n) := by
  let oddSeries : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (2*n+1), (-1)^k*a k
  let evenSeries : ℕ → ℝ := fun n => ∑ k ∈ Finset.range (2*n), (-1)^k*a k
  have hanpos := AntitoneLimitBound ha aLim

  have hOddAnti := AntitoneSeriesOdd ha hanpos
  have hOddBdd := BddSeriesOdd ha hanpos
  have hOddConv := SeqConv_of_AntitoneBdd oddSeries 0 hOddBdd hOddAnti
  rcases hOddConv with ⟨Lodd, hLodd⟩

  have hEvenMono := MonotoneSeriesEven ha hanpos
  have hEvenBdd := BddSeriesEven ha hanpos
  have hEvenConv := SeqConv_of_MonotoneBdd evenSeries (a 0) hEvenBdd hEvenMono
  rcases hEvenConv with ⟨Leven, hLeven⟩

  have hLSame := CoherenceOfReals hLodd hLeven (DiffGoesToZero aLim)
  rewrite[hLSame] at hLodd

  exact ⟨Leven, SeqEvenOdd hLeven hLodd⟩

theorem Monotone_of_NonNegSeries {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) : Monotone (Series a) := by
  apply monotone_nat_of_le_succ
  intro n
  unfold Series
  rewrite[sum_range_succ]
  bound

theorem MonotoneLimitBound {a : ℕ → ℝ} (amono : Monotone a) {L : ℝ} (ha : SeqLim a L) : ∀ n, a n ≤ L := by
  by_contra hc
  push Not at hc
  rcases hc with ⟨N, hN⟩
  rcases ha (a N - L) (by bound) with ⟨M, hM⟩
  have hMax := hM (M + N) (by bound)
  have hMaxGeN := amono (show N ≤ M + N by bound)
  have hMaxGeL : a (M + N) > L := by bound
  have hAbs : |a (M + N) - L| = a (M + N) - L := by apply abs_of_nonneg (le_of_lt (show a (M + N) - L > 0 by bound))
  rewrite[hAbs] at hMax
  bound

theorem ComparisonTest {a b : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (hab : ∀ n, a n ≤ b n) (hb : SeriesConv b) : SeriesConv a := by
  have hs : ∀ n, Series a n ≤ Series b n := SeriesOrderThm hab
  have hmonoa : Monotone (Series a) := by
    apply monotone_nat_of_le_succ
    intro n
    unfold Series
    rewrite[sum_range_succ]
    norm_num
    exact ha n

  have hmonob : Monotone (Series b) := by
    apply monotone_nat_of_le_succ
    intro n
    unfold Series
    rewrite[sum_range_succ]
    simp
    linarith[ha n, hab n]

  rcases hb with ⟨L, hL⟩
  have hsb : ∀ n : ℕ, Series b n ≤ L := MonotoneLimitBound hmonob hL

  apply SeqConv_of_MonotoneBdd (Series a) L ?_ hmonoa
  intro n
  linarith[hsb n, hs n]

theorem StrongCauchy_of_AbsSeriesConv {a : ℕ → ℝ} (ha : AbsSeriesConv a) {ε : ℝ} (hε : ε > 0) : ∃ N, ∀ (S : Finset ℕ), (∀ k ∈ S, k ≥ N) → ∑ k ∈ S, |a k| < ε := by
  rcases ha with ⟨L, hL⟩
  rcases hL (ε/2) (by bound) with ⟨N, hN⟩
  refine ⟨N, fun S hS => ?_⟩
  rcases S.eq_empty_or_nonempty with hSe | hSne
  · bound
  · rcases hSne with ⟨k0, hk0⟩
    set M := S.sup id + 1 with hMdef
    have hM : ∀ k ∈ S, k < M := by
      intro k hk
      have := Finset.le_sup (f := id) hk
      rewrite[id_eq] at this
      bound
    have hNM : N ≤ M := le_trans (hS k0 hk0) (le_of_lt (hM k0 hk0))
    have hSsub : S ⊆ Finset.Ico N M := by
      intro k hk
      apply Finset.mem_Ico.mpr ⟨(hS k hk), (hM k hk)⟩
    have hIco : ∑ k ∈ S, |a k| ≤ ∑ k ∈ Finset.Ico N M, |a k| := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hSsub
      intro i _ _
      apply abs_nonneg
    have hIcoSeries : Series (fun n => |a n|) M - Series (fun n => |a n|) N = ∑ k ∈ Finset.Ico N M, |a k| := DiffOfSeries (fun n => |a n|) hNM
    rewrite[← hIcoSeries] at hIco
    have htri : Series (fun n => |a n|) M - Series (fun n => |a n|) N
    ≤ |Series (fun n => |a n|) M - L| + |Series (fun n => |a n|) N - L| := by
      calc
        Series (fun n => |a n|) M - Series (fun n => |a n|) N ≤ |Series (fun n => |a n|) M - Series (fun n => |a n|) N| := le_abs_self _
        _ ≤ |Series (fun n => |a n|) M - L| + |L - Series (fun n => |a n|) N| := abs_sub_le _ _ _
-- 没想到 rewrite 和 rw 还有些区别，rw = rewrite + rfl
        _ = |Series (fun n => |a n|) M - L| + |Series (fun n => |a n|) N - L| := by rw[abs_sub_comm L];
    have h1 : |Series (fun n => |a n|) M - L| < ε/2 := hN M hNM
    have h2 : |Series (fun n => |a n|) N - L| < ε/2 := hN N le_rfl

    bound

-- def Injective (f : X → Y) := ∀ i j : X, f i = f j → i = j
-- def Surjective (f : X → Y) := ∀ y : Y, ∃ x : X, f x = y
def Rearrangement (f : X → Y) := Function.Injective f ∧ Function.Surjective f

theorem EventuallyCovers_of_Rearrangement {σ : ℕ → ℕ} (hσ : Rearrangement σ) (M : ℕ) : ∃ N, ∀ n ≥ N, (range M) ⊆ image σ (range n) := by
  choose σᵥ hσᵥ using hσ.2
  set N := (image σᵥ (range M)).sup id + 1 with hNdef
  refine ⟨N, fun n hn m hm => ?_⟩
  simp only [mem_range, mem_image] at hm ⊢
  refine ⟨σᵥ m, ⟨?_, (by bound)⟩⟩
  have hle : σᵥ m ≤ (image σᵥ (range M)).sup id := by
    apply Finset.le_sup (f := id)
    apply Finset.mem_image_of_mem
    apply Finset.mem_range.mpr hm
-- -- 可以直接合并成下面一句
--     -- Finset.le_sup (f := id) (Finset.mem_image_of_mem f (Finset.mem_range.mpr hm))
  bound

theorem Series_image (a : ℕ → ℝ) (σ : ℕ → ℕ) (hσ : Function.Injective σ) (n : ℕ) : Series (a ∘ σ) n = ∑ k ∈ Finset.image σ (Finset.range n), a k :=
  (Finset.sum_image (fun _ _ _ _ hxy => hσ hxy)).symm

theorem RearrangementThm {a : ℕ → ℝ} (ha : AbsSeriesConv a) : ∃ L, ∀ (σ : ℕ → ℕ) (_ : Rearrangement σ), SeriesLim (a ∘ σ) L := by
  rcases Conv_of_AbsSeriesConv ha with ⟨L, hL⟩
-- 居然还能这么写
  refine ⟨L, fun σ hσ => fun ε hε => ?_⟩

  rcases StrongCauchy_of_AbsSeriesConv ha (show ε/2 > 0 by positivity) with ⟨N1, hN1⟩
  rcases hL (ε/2) (by bound) with ⟨N2, hN2⟩

  set N3 := N1 + N2 with hN3def
  rcases EventuallyCovers_of_Rearrangement hσ N3 with ⟨N4, hN4⟩

  refine ⟨N4, fun n hn => ?_⟩
  set T := image σ (range n) \ range N3  with hTdef
  have hSplit : Series (a ∘ σ) n = (∑ k ∈ T, a k) + Series a N3 := by
    rewrite[Series_image a σ hσ.1]
    have hs : ∑ k ∈ image σ (range n), a k = ∑ k ∈ T, a k  + ∑ k ∈ range N3, a k :=  by
-- 加了symm就是等号左右两边换个位置
      apply (sum_sdiff (hN4 n hn)).symm
    rewrite[hs]
    bound
  have hN3 : |Series a N3 - L| < ε/2 := hN2 N3 (by bound)
  have hAbs : |∑ k ∈ T, a k| < ε/2 :=  by
    have _h1 : |∑ k ∈ T, a k| ≤ ∑ k ∈ T, |a k| := abs_sum_le_sum_abs a T
    have hT : ∑ k ∈ T, |a k|  < ε/2  := by
      apply hN1 T
      intro k hk
      rewrite[hTdef] at hk
      rewrite[mem_sdiff] at hk
      rewrite[mem_range] at hk
      bound
    bound
  calc
    |Series (a ∘ σ)  n -  L| = |((∑ k ∈ T, a k) + Series a N3  - L)| := by rw[hSplit]
    _ = |((∑ k ∈ T, a k) + (Series a N3  - L))| := by ring_nf
    _ ≤ |∑ k ∈ T, a k| + |Series a N3 - L| := by apply abs_add_le
    _ < ε/2 + ε/2 := by bound
    _ = ε := by bound


example {a : ℕ → ℝ} (ha1 : SeriesConv a) (ha2 : ¬ AbsSeriesConv a) : ∀ L, ∃ (σ : ℕ → ℕ) (hσ : Rearrangement σ), SeriesLim (a ∘ σ) L := by sorry

def FunLimAt (f : ℝ → ℝ) (L c : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x - L| < ε

example : ∃ L, FunLimAt (fun x ↦ (x^2 - 1)/(x - 1)) L 1 := by
  use 2
  intro ε hε
-- 像 ∃δ > 0 这个结论，refine 的时候，既要给出 δ 也要给出 δ > 0
  refine ⟨ε, hε, fun x hx hxδ => ?_⟩
  have hsimp : (x^2 - 1) / (x - 1) = x + 1 := by
    field_simp
    -- have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    -- rw [div_eq_iff hx1]
    ring_nf

  simp only
  rw [hsimp]
  have heq : x + 1 - 2 = x - 1 := by ring
  rw [heq]
  exact hxδ

def FunContAt (f : ℝ → ℝ) (c : ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x, |x - c| < δ → |f x - f c| < ε

example : FunContAt (fun x ↦ x^2 - 1) 2 := by
  intro ε hε
  set δ := min 1 (ε/5) with hδdef
  have hδ : δ > 0 := by bound
  refine ⟨δ, hδ, fun x hx => ?_⟩
  simp only
  norm_num
  have heq : |x^2 - 1 - 3| = |x + 2| * |x -2| := by
    calc
      |x^2 - 1 - 3| = |(x+2) * (x-2)| := by ring_nf
      _ = |x + 2| * |x - 2| := by apply abs_mul
  rewrite[heq]
  have hδLt1 : δ ≤ 1 := by bound
  have hx1 : |x - 2| < 1 := by bound
  have hx2 : |x + 2| < 5 := by
    calc
      |x + 2| = |x - 2 + 4| := by ring_nf
      _ ≤ |x - 2| + |4| := by apply abs_add_le
      _ < 1 + |4| := by bound
      _ = 1 + 4 := by bound
      _ = 5 := by ring_nf
  have hδLtε : δ ≤ ε/5 := by bound
  have hx3 : |x - 2| < ε/5 := by bound
  calc
    |x + 2| * |x - 2| < 5 * (ε/5):= by
      apply mul_lt_mul' (le_of_lt hx2) hx3 (abs_nonneg _) (by bound)
    _ = ε := by ring_nf

theorem FunContAtAdd {f g : ℝ → ℝ} {c : ℝ} (hf : FunContAt f c) (hg : FunContAt g c) : FunContAt (fun x ↦ f x + g x) c := by
  intro ε hε
  rcases hf (ε/2) (by positivity) with ⟨δ1, ⟨hδ11, hδ12⟩⟩
  rcases hg (ε/2) (by positivity) with ⟨δ2, ⟨hδ21, hδ22⟩⟩
  set δ := min δ1 δ2 with hδdef
  have hδ : δ > 0 := by bound
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hfxc : |f x - f c| < ε/2 := by
    have : δ ≤ δ1 := by bound
    have : |x - c| < δ1 := by bound
    bound
  have hgxc : |g x - g c| < ε/2 := by
    have : δ ≤ δ2 := by bound
    have : |x - c| < δ2 := by bound
    bound
  simp only
  calc
    |f x + g x - (f c + g c)| = |f x - f c + (g x - g c)| := by ring_nf
    _ ≤ |f x - f c| + |g x - g c| := by apply abs_add_le
    _ < (ε/2) + (ε/2) := by bound
    _ = ε := by bound

theorem SeqLim_of_FunLimAt {f : ℝ → ℝ} {L c : ℝ} (hf : FunLimAt f L c) : ∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLim x c → SeqLim (fun n ↦ f (x n)) L := by
  intro x hxn hxc ε hε
  rcases hf ε hε with ⟨δ, ⟨hδ, hfδ⟩⟩
  rcases hxc δ hδ with ⟨N, hN⟩
  refine ⟨N, fun n hn => ?_⟩
  -- simp only
  exact hfδ (x n) (hxn n) (hN n hn)

example (f : ℝ → ℝ) (c : ℝ) (hf : FunContAt f c) : FunLimAt f (f c) c := by
  intro ε hε
  rcases hf ε hε with ⟨δ, ⟨hδ, hfδ⟩⟩
  refine ⟨δ, hδ, fun x hx1 hx2 => ?_⟩
  exact hfδ x hx2

example (f : ℝ → ℝ) (c : ℝ) (hf : FunLimAt f (f c) c) : FunContAt f c := by
  intro ε hε
  rcases hf ε hε with ⟨δ, ⟨hδ, hfδ⟩⟩
  refine ⟨δ, hδ, fun x hx => ?_⟩
-- 有点笨了，既然 x 可以取到 c ，那么分类讨论就可以了，居然还在那里找 x ≠ c 的条件
  by_cases hxc : x = c
  · rewrite[hxc]
    -- simp[hε]
    norm_num[hε]
  · exact hfδ x hxc hx

theorem ConstTimesLimAt (f : ℝ → ℝ) (c L k : ℝ) (hf : FunLimAt f L c) : FunLimAt (fun x ↦ k * f x) (k * L) c := by
  intro ε hε
  by_cases hk : k = 0
  · rewrite[hk]
    simp only
    norm_num
    use 1
    bound
  · have hεk : ε/|k| > 0 := by positivity
    rcases hf (ε/|k|) hεk with ⟨δ, ⟨hδ, hfδ⟩⟩
    refine ⟨δ, hδ, fun x hx1 hx2 => ?_⟩
    simp only
    have heq : |k * f x - k * L| = |k| * |f x - L| := by
      calc
        |k * f x - k * L| = |k * (f x - L)| := by ring_nf
        _ = |k| * |f x - L| := by apply abs_mul
    rewrite[heq]
    have hfxL : |f x - L| < ε/|k| := hfδ x hx1 hx2
    field_simp at hfxL
    bound

theorem Bdd_of_LimAt (f : ℝ → ℝ) (c L : ℝ) (hf : FunLimAt f L c) : ∃ M > 0, ∃ δ > 0, ∀ x ≠ c, |x - c| < δ → |f x| < M := by
  rcases hf 1 (by bound) with ⟨δ, ⟨hδ, hfδ⟩⟩
  refine ⟨|L| + 2, (by positivity), δ, hδ, fun x hx1 hx2 => ?_⟩
  have fxL : |f x - L| < 1 := hfδ x hx1 hx2
  calc
    |f x| = |f x - L + L| := by ring_nf
    _ ≤ |f x - L| + |L| := by apply abs_add_le
    _ < 1 + |L| := by bound
    _ < |L| + 2 := by bound

theorem FunLim_of_SeqLim {f : ℝ → ℝ} {L c : ℝ} (h : ∀ x : ℕ → ℝ, (∀ n, x n ≠ c) → SeqLim x c → SeqLim (fun n ↦ f (x n)) L) : FunLimAt f L c := by
  by_contra hcon
  unfold FunLimAt at hcon
  push Not at hcon
  rcases hcon with ⟨ε, ⟨hε, hδ⟩⟩
-- 原来是通过这种方式构建数列的呀
  have hchoice : ∀ n : ℕ, ∃ x, x ≠ c ∧ |x - c| < 1 / (n + 1) ∧ ε ≤ |f x - L| := fun n => hδ (1/(n+1)) (by positivity)
  choose xs hxs1 hxs2 hxs3 using hchoice
  have hxsc : SeqLim xs c := by
    intro ε' hε'
    -- obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε')
    rcases ArchProp hε' with ⟨N, hN⟩
    refine ⟨N, fun n hn => ?_⟩
    have _h1 : |xs n - c| < 1/(n+1) := hxs2 n
    have _h2 : (1:ℝ)/(n+1) ≤ 1/(N + 1) := by
      have : 0 < 1/ε' := by field_simp; bound
      apply one_div_le_one_div_of_le (by linarith)
      have : N + 1 ≤ n + 1 := by bound
      exact_mod_cast this
    have _h3 : (1:ℝ)/(N+1) < ε' := by
      field_simp
      field_simp at hN
      linarith
    linarith

  rcases h xs hxs1 hxsc ε hε with ⟨N, hN⟩
  have h1 := hN N (by bound)
  have h2 := hxs3 N
  bound

def FunDerivAt (f : ℝ → ℝ) (L c : ℝ) := FunLimAt (fun h ↦ (f (c + h) - f c) / h) L 0

example : FunDerivAt (fun x ↦ x^2 - 1) 4 2 := by
  intro ε hε
  refine ⟨ε, hε, fun x hx1 hx2 => ?_⟩
  simp only
  have heq : (x^2 + 4 * x)/x = x+4 := by field_simp
  ring_nf at hx2
  calc
  |((2 + x) ^ 2 - 1 - (2 ^ 2 - 1)) / x - 4| = |(x^2 + 4*x)/x - 4| := by ring_nf
  _ = |(x + 4) - 4| := by rw[heq]
  _ = |x| := by bound
  _ < ε := by bound

def FunDeriv (f : ℝ → ℝ) (g : ℝ → ℝ) := ∀ x, FunDerivAt f (g x) x

example (f g : ℝ → ℝ) (hf : ∀ x, f x = x ^ 2 - 1) (hg : ∀ x, g x = 2 * x) : FunDeriv f g := by
  intro c ε hε
  refine ⟨ε, hε, fun x hx1 hx2 => ?_⟩
  ring_nf at hx2
  simp only
  rewrite[hf c, hf (c + x), hg c]
  have heq : (x^2+2*c*x)/x = x + 2*c := by field_simp
  calc
  |((c + x) ^ 2 - 1 - (c ^ 2 - 1)) / x - 2 * c| = |(x^2 + 2 * c * x)/x - 2 * c| := by ring_nf
  _ = |x+2*c - 2 * c| := by rw[heq]
  _ = |x| := by bound
  _ < ε := by bound

def FunCont (f : ℝ → ℝ) := ∀ x, FunContAt f x

example : FunCont (fun x ↦ x^2 - 1) := by
  intro c ε hε
-- 因为 c 有可能是 0 ，所以需要 +1
  set δ := min 1 (ε/(2*|c| + 1)) with hδdef
  have hδ : δ > 0 := by positivity
  refine ⟨δ, hδ, fun x hx => ?_⟩
  simp only
  ring_nf
  by_cases hxc : x = c
  · rewrite[hxc]
    norm_num
    bound
  · have hxpc : |x + c| < 2*|c| + 1 := by
      have : δ ≤ 1 := by bound
      calc
      |x + c| = |x - c + 2 * c| := by ring_nf
      _ ≤ |x - c| + |2 * c| := by apply abs_add_le
      _ < δ + |2*c| := by bound
      _ ≤ 1 + |2*c| := by bound
      _ = |2*c| + 1 := by bound
      _ = 2*|c| + 1 := by bound
    have hδLe1 : δ ≤ (ε/(2*|c|+1)) := by bound
    have hδLe2 : |x - c| < (ε/(2*|c|+1)) := by bound
    have hxc0 : |x - c| > 0 := by
      have : x - c ≠ 0 := by bound
      apply abs_pos.mpr this
    calc
    |x ^ 2 - c^2| = |(x +c)*(x -c)| := by ring_nf
    _ = |x + c| * |x - c| := by apply abs_mul
    _ < (2*|c| + 1) * (ε/(2*|c|+1)) := by
      apply mul_lt_mul hxpc (le_of_lt hδLe2) hxc0 (by bound)
    _ = ε := by field_simp

theorem Cont_Comp (f g : ℝ → ℝ) (hf : FunCont f) (hg : FunCont g) : FunCont (f ∘ g) := by
  intro c ε hε
  rcases hf (g c) ε hε with ⟨δf, hδf1, hδf2⟩
  rcases hg c δf hδf1 with ⟨δg, hδg1, hδg2⟩
  refine ⟨δg, hδg1, fun x hx => ?_⟩
  specialize hδg2 x hx
  specialize hδf2 (g x) hδg2
  bound

def UnifConv (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) := ∀ ε > 0, ∃ N, ∀ n ≥ N, ∀ x, |f n x - F x| < ε

theorem Cont_of_UnifConv (f : ℕ → ℝ → ℝ) (hf : ∀ n, FunCont (f n)) (F : ℝ → ℝ) (hfF : UnifConv f F) : FunCont F := by
  intro c ε hε
  rcases hfF (ε/3) (by positivity) with ⟨N, hN⟩
  rcases (hf N c) (ε/3) (by positivity) with ⟨δ, hδ1, hδf⟩
  refine ⟨δ, hδ1, fun x hx => ?_⟩
  have hfNx := hN N (by bound) x
  have hfNc := hN N (by bound) c
  specialize hδf x hx
  have htri : |f N  x -  F c| ≤ |f N x - f N c| + |f N c - F c| := abs_sub_le _ _ _
  calc
  |F x - F c| ≤ |F x - f N x| + |f N x - F c| := abs_sub_le _ _ _
  _ = |f N x - F x| + |f N x - F c| := by rw[abs_sub_comm (F x)]
  _ ≤ |f N x - F x| + |f N x - f N c| + |f N c - F c| := by linarith
  _ < ε/3 + ε/3 + ε/3 := by linarith
  _ = ε := by bound

noncomputable def RiemannSum (f : ℝ → ℝ) (a b : ℝ) (N : ℕ) := (b - a) / N * ∑ i ∈ range N, f (a + (i + 1) * (b - a) / N)
def HasIntegral (f : ℝ → ℝ) (a b : ℝ) (I : ℝ) := SeqLim (fun N ↦ RiemannSum f a b N) I
def IntegrableOn (f : ℝ → ℝ) (a b : ℝ) := ∃ I, HasIntegral f a b I

-- theorem card_range (n : ℕ) : (Finset.range n).card = n := by sorry
-- theorem sum_add_distrib {ι} {M} {s : Finset ι} [AddCommMonoid M] {f g : ι → M} : ∑ x ∈ s, (f x + g x) = ∑ x ∈ s, f x + ∑ x ∈ s, g x := by sorry
-- theorem sum_const {ι} {M} {s : Finset ι} [AddCommMonoid M] (b : ℝ) : ∑ _x ∈ s, b = s.card * b := by sorry
-- theorem sum_div {ι} {K} [DivisionSemiring K] (s : Finset ι) (f : ι → K) (a : K) : (∑ i ∈ s, f i) / a = ∑ i ∈ s, f i / a := by sorry
-- theorem sum_mul {ι} {R} [NonUnitalNonAssocSemiring R] (s : Finset ι) (f : ι → R) (a : R) : (∑ i ∈ s, f i) * a = ∑ i ∈ s, f i * a := by sorry
theorem sum_range_add_one (n : ℕ) : ∑ i ∈ Finset.range n, ((i:ℝ) + 1) = n * (n + 1) / 2 := by
  induction n with
  | zero => bound
  | succ n hn =>
    rewrite[sum_range_succ, hn]
    field_simp
    norm_num
    bound



example {a b : ℝ} (hab : a < b) : IntegrableOn (fun x ↦ x) a b := by
  set L := (b^2-a^2)/2 with hLdef
  refine ⟨L, fun ε hε => ?_⟩
  rcases exists_nat_gt ((a-b)^2/(2*ε)) with ⟨K, hK⟩
  refine ⟨max 1 K, fun n hn => ?_⟩
  unfold RiemannSum
  simp only

  have hngt0 : n > 0 := by omega
  have hsplit : ∑ i ∈ Finset.range n, (a + ((i:ℝ) + 1) * (b - a) / n)
        = (n : ℝ) * a + (b - a) * ((n + 1) / 2) := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    -- congr
    rw[← Finset.sum_div]
    rw[← Finset.sum_mul]
    rw[sum_range_add_one]
    field_simp
  rewrite[hsplit]
  have heq : (b - a) / (n:ℝ) * ((n:ℝ) * a + (b - a) * ((n + 1) / 2)) - (b^2-a^2)/2 = (a-b)^2/(2*n) := by field_simp;ring_nf
  rewrite[heq]
  have hpos : (a-b)^2/(2*(n:ℝ)) > 0 := by
    have : a - b ≠ 0 := by bound
    have : (a-b)^2 > 0 := by positivity
    bound
  rewrite[abs_of_pos hpos]

  have hngeK : n ≥ K := by omega
  have hRngeK : (n:ℝ) ≥ (K:ℝ) := by exact_mod_cast hngeK
  have hngtε : n > (a-b)^2/(2*ε) := by bound
  field_simp at hngtε
  field_simp
  rewrite[mul_assoc, mul_comm (n:ℝ), ← mul_assoc]
  bound

example (f : ℕ → ℝ → ℝ) (F : ℝ → ℝ) (hfF : UnifConv f F) : ∀ x, SeqLim (fun n ↦ f n x) (F x) := by
  intro x ε hε
  rcases hfF ε hε with ⟨N, hN⟩
  refine ⟨N, (by bound)⟩

example : FunCont (fun x ↦ x ^ 3) := by
  intro c ε hε
  simp only
-- x^3 - c^3 = (x-c)(x^2+xc+c^2) < ε
-- 也先 δ ≤ 1 粗略地把 x 限制在 c 的附近，那么就有（只需要粗略放大就可以了）
-- x^2 ≤ (|c| + 1)^2
-- xc ≤ (|c| + 1)^2
-- c^2 ≤ (|c| + 1)^2
-- 也即 x^3-c^3 ≤ (x-c)(3 * (|c|+1)^2)
-- 那么要求 x^3-c^3 < ε ，只需要 (x-c)(3 * (|c|+1)^2) < ε，也即 x-c < ε/(3 * (|c|+1)^2)，即
-- 取 δ = ε/(3 * (|c|+1)^2)
  set B := 3 * (|c|+1)^2
  set δ := min 1 ε/B with hδdef
  have hδ : δ > 0 := by positivity
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have hδ1 : δ ≤ 1 := by bound
  have hxc :|x| ≤ |c| + 1 := by
    calc
      |x| = |x - c + c| := by bound
      _ ≤ |x - c| + |c| := abs_add_le _ _
      _ ≤ 1 + |c| := by bound
      _ = |c| + 1 := by bound
  have hs1 : |x^2| ≤ (|c| + 1)^2 := by
    have : |x|^2 ≤ (|c| + 1)^2 := by bound
    rewrite[show |x^2| = |x|^2 by bound]
    bound
  have hs2 : |x * c| ≤ (|c| + 1)^2 := by
    calc
    |x * c| = |x| * |c| := by apply abs_mul
    _ ≤ (|c| + 1) * (|c| + 1) := by bound
    _ = (|c| + 1)^2 := by bound
  have hs3 : |c^2| < (|c| + 1)^2 := by
    calc
    |c^2| = |c|^2 := by bound
    _ < (|c| + 1)^2 := by bound
  have hs : |x^2 + x*c + c^2| < B := by
    calc
    |x^2 + x*c + c^2| ≤ |x^2 + x*c| + |c^2| := abs_add_le _ _
    _ ≤ |x^2| + |x*c| + |c^2| := by
      have : |x^2 + x*c| ≤ |x^2| + |x*c| := abs_add_le _ _
      bound
    _ < (|c|+1)^2 + (|c|+1)^2 + (|c|+1)^2 := by bound
    _ = B := by bound
  calc
  |x^3 - c^3| = |(x-c) * (x^2 + x*c + c^2)| := by ring_nf
  _ = |x - c| * |x^2 + x*c + c^2| := abs_mul _ _
  _ < (ε/B) * B := by
    have : δ ≤ ε/B := by bound
    have hxcεB: |x - c| < ε/B := by bound
    apply mul_lt_mul'' hxcεB hs (by positivity) (by positivity)
  _ = ε := by
    have : B > 0 := by positivity
    field_simp

example : ∃ g : ℝ → ℝ, FunDeriv (fun x ↦ x ^ 3) g := by
  set g : ℝ → ℝ := fun x => 3*x^2 with hgdef
  refine ⟨g, fun c ε hε => ?_⟩
-- 经过可知不等号左边等于 |dx^2 + 3 * dx * c| = |dx|*|dx+3c|
-- 还是先用 δ ≤ 1，把 x 控制在 c 的附近，即
-- dx ≤ 1
-- |dx + 3c| < 3*|c| + 1
-- 则要想 |dx| * |dx+3c| < ε，只需要 |dx| * (3*|c| + 1)< ε，也即 δ < ε/(3*|c|+1)
  set B := ε/(3*|c|+1)
  refine ⟨min 1 B, (by positivity), fun dx hdx1 hdx2 => ?_⟩
  simp only
  norm_num at hdx2
  calc
  |((c + dx) ^ 3 - c ^ 3) / dx - g c| = |((c + dx) ^ 3 - c ^ 3) / dx - 3*c^2| := by bound
  _ = |dx^2 + 3*dx*c| := by
    have : (c+dx)^3 - c^3 = dx*(dx^2+3*dx*c+3*c^2) := by ring_nf
    rewrite[this]
    have : (dx*(dx^2+3*dx*c+3*c^2))/dx = dx^2+3*dx*c+3*c^2 := by field_simp
    rewrite[this]
    bound
  _ = |dx*(dx+3*c)| := by ring_nf
  _ = |dx| * |dx+3*c| := abs_mul _ _
  _ < B * (3*|c| + 1) := by
    have : |dx| < 1 := by bound
    have : |dx + 3*c| ≤ |dx| + |3*c| := abs_add_le _ _
    have : |3*c| = 3*|c| := by bound
    have : |dx| + |3*c| < 1 + 3*|c| := by bound
    apply mul_lt_mul'' (by bound) (by bound) (by positivity) (by positivity)
  _ = ε/(3*|c|+1) * (3*|c|+1) := by bound
  _ = ε := by field_simp


theorem sum_of_squares (n : ℕ) : ∑ i ∈ Finset.range n, ((i : ℝ) + 1) ^ 2 = ((n : ℝ) * (n + 1) * (2 * n + 1)) / 6 := by
  induction n with
  | zero => bound
  | succ n hn =>
  rewrite[sum_range_succ, hn]
  push_cast
  have h3 : ((n+1):ℝ) * (((n):ℝ)+1+1) * (2*((n:ℝ)+1)+1) = 2*n^3+9*n^2+13*n+6 := by ring_nf
  rewrite[h3]
  ring_nf

theorem hxabThm (a b D : ℝ) (i j k n : ℕ) (hi : i < n) (hj : j < k) (hab : a < b) (hk : k ≠ 0) (hn : n ≠ 0) (hD : D = (b-a)/n) :
(((k:ℝ) * a + D * ((k:ℝ) * (i:ℝ) + (j:ℝ) + 1)) / (k:ℝ)) ∈ Set.Icc a b := by
  have : (((k:ℝ) * a + D * ((k:ℝ) * (i:ℝ) + (j:ℝ) + 1)) / (k:ℝ)) = a + D *(i:ℝ) + D * ((j:ℝ)+1)/(k:ℝ) := by
    field_simp
    ring_nf
  rewrite[this]
  have hDpos : D > 0 := by field_simp; bound
  constructor
  · have : D * (i:ℝ) ≥ 0 := by positivity
    have : D * ((j:ℝ)+1)/(k:ℝ) ≥ 0 := by positivity
    bound
  · have hin : i + 1 ≤ n := by bound
    have hinr: (i:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hin
    have hjk : j + 1 ≤ k := by bound
    have hjkr : (j:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hjk
    have hjdkr: ((j:ℝ) + 1)/(k:ℝ) ≤ 1 := by bound
    have : (i:ℝ) + ((j:ℝ) + 1)/(k:ℝ) ≤ (n:ℝ) := by bound
    have : D * (i:ℝ) + D * ((j:ℝ) + 1) / (k:ℝ) = D * ((i:ℝ) + ((j:ℝ) + 1)/(k:ℝ)) := by field_simp
    rewrite[add_assoc, this]
    have : D * ((i:ℝ) + ((j:ℝ) + 1)/(k:ℝ)) ≤ D * (n:ℝ) := by bound
    nth_rewrite 2 [hD] at this
    field_simp at this
    field_simp
    bound

theorem hyabThm (a b D : ℝ) (i n : ℕ) (hi : i < n) (hab : a < b) (hn : n ≠ 0) (hD : D = (b-a)/n) :
(a + D * ((i:ℝ) + 1)) ∈ Set.Icc a b := by
  constructor
  · bound
  · have hin : i + 1 ≤ n := by bound
    have hinr: (i:ℝ) + 1 ≤ (n:ℝ) := by exact_mod_cast hin
    have : D * ((i:ℝ) + 1) ≤ D * (n:ℝ) := by bound
    nth_rewrite 2 [hD] at this
    field_simp at this
    bound

theorem hxyδThm (a b D δ : ℝ) (i j k n : ℕ) (hi : i < n) (hj : j < k) (hab : a < b) (hk : k ≠ 0) (hn : n ≠ 0) (hD : D = (b-a)/n) (hfine : 2 * (b - a) / n < δ) :
|(((k:ℝ) * a + D * ((k:ℝ) * (i:ℝ) + (j:ℝ) + 1)) / (k:ℝ)) - (a + D * ((i:ℝ) + 1))| < δ := by
  have hDpos : D > 0 := by field_simp; bound
  have hjk : j + 1 ≤ k := by bound
  have hjkr : (j:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hjk
  have hjdkr: ((j:ℝ) + 1)/(k:ℝ) ≤ 1 := by bound

  have : (((k:ℝ) * a + D * ((k:ℝ) * (i:ℝ) + (j:ℝ) + 1)) / (k:ℝ)) - (a + D * ((i:ℝ) + 1)) = D * ((j:ℝ) + 1)/(k:ℝ) - D := by field_simp;bound
  rewrite[this, abs_sub_comm]
  have : D - D * ((j:ℝ)+1)/(k:ℝ) = D * (1-((j:ℝ)+1)/(k:ℝ)) := by ring_nf
  rewrite[this]
  have : |1-((j:ℝ)+1)/(k:ℝ)| ≤ 2 := by
    have : ((j:ℝ)+1)/(k:ℝ) > 0 := by bound
    have : |((j:ℝ)+1)/(k:ℝ)| = ((j:ℝ)+1)/(k:ℝ) := abs_of_pos this
    calc
    _ ≤ |1| + |((j:ℝ)+1)/(k:ℝ)| := by apply abs_sub
    _ = 1 + |((j:ℝ)+1)/(k:ℝ)| := by bound
    _ = 1 + ((j:ℝ)+1)/(k:ℝ) := by rw[this]
    _ ≤ 1 + 1 := by bound
    _ ≤ 2 := by bound
  have : |D| = D := abs_of_pos hDpos
  calc
  |D * (1 - ((j:ℝ) + 1) / (k:ℝ))| = |D| * |1- ((j:ℝ)+1)/(k:ℝ)| := by apply abs_mul
  _ ≤ |D| * 2 := by bound
  _ = D * 2 := by bound
  _ = 2 * (b - a) / (n:ℝ) := by rewrite[hD];field_simp;
  _ < δ := by bound

theorem RiemannSumRefinement (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) {n k : ℕ} (hn : n ≠ 0) (hk : k ≠ 0) {ε δ : ℝ} (_ : ε > 0) (_ : δ > 0)
(hunif : ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |y - x| < δ → |f y - f x| < ε) (hfine : 2 * (b - a) / n < δ) :
|RiemannSum f a b (n * k) - RiemannSum f a b n| < (b - a) * ε := by
  set D := (b-a)/n with hDdef
  have hDpos : D > 0 := by positivity
  have hkpos : k > 0 := by positivity
  unfold RiemannSum
  have hreindex : ∀ g : ℕ → ℝ,
      ∑ m ∈ Finset.range (n * k), g m
        = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range k, g (i * k + j) := by
    intro g
    rw [← Finset.sum_product']
    apply Finset.sum_nbij' (fun m => (m / k, m % k)) (fun p => p.1 * k + p.2)
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [Finset.mem_product, Finset.mem_range]
      exact ⟨Nat.div_lt_of_lt_mul (by rwa [mul_comm] at hm), Nat.mod_lt m hkpos⟩
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      simp only [Finset.mem_range]
      calc p.1 * k + p.2 < p.1 * k + k := by omega
        _ = (p.1 + 1) * k := by ring
        _ ≤ n * k := by apply Nat.mul_le_mul_right; omega
    · intro m hm
      rewrite[mul_comm]
      exact Nat.div_add_mod m k
    · intro p hp
      simp only [Finset.mem_product, Finset.mem_range] at hp
      ext
      · have _h1 : ((p.1 * k + p.2) / k, (p.1 * k + p.2) % k).1 = (p.1 * k + p.2) / k := by bound
        rewrite[_h1]
        have _h2 : p.2 / k = 0 := Nat.div_eq_of_lt hp.2
        rewrite[add_comm, mul_comm]
        have _h3 : (p.2 + k * p.1) / k = p.2/k + p.1 := Nat.add_mul_div_left _ _ hkpos
        bound
      · simp [Nat.mod_eq_of_lt hp.2]
    · intro m hm
      simp only
      rewrite[mul_comm]
      have : k*(m/k)+m%k = m := Nat.div_add_mod m k
      rewrite[this]
      rfl

  rewrite[hreindex]
  have hDba : b - a = D * n := by field_simp at hDdef; bound
  have hDk : (b-a)/(n*k) = D/k := by field_simp; bound
  push_cast
  rewrite[hDk, hDba]
  rewrite[mul_sum, mul_sum, ← sum_sub_distrib]
  have hDnε : D * (n:ℝ) * ε = ∑ _ ∈ range n, D * ε := by
    rewrite[sum_const, card_range, nsmul_eq_mul]
    bound
  rewrite[hDnε]
  rewrite[abs_lt]
  constructor
  · have : - ∑ x ∈ range n, D * ε = ∑ x ∈ range n, -D * ε := by bound
    rewrite[this]
    apply sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hn)
    intro i hi
    rewrite[mem_range] at hi
    field_simp
    rewrite[show -(ε*(k:ℝ)) = ∑ x ∈ range k, (-ε) by rw[sum_const, card_range, nsmul_eq_mul];ring_nf]
    rewrite[show (k:ℝ) * f (a + D * ((i:ℝ) + 1)) = ∑ x ∈ range k, f (a + D * ((i:ℝ) + 1)) by rw[sum_const, card_range, nsmul_eq_mul]]
    rewrite[← sum_sub_distrib]
    apply sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hk)
    intro j hj
    rewrite[mem_range] at hj
    have hxab := hxabThm a b D i j k n hi hj hab hk hn hDdef
    have hyab := hyabThm a b D i n hi hab hn hDdef
    have hxyδ := hxyδThm a b D δ i j k n hi hj hab hk hn hDdef hfine

    have fyx := hunif _ hyab _ hxab hxyδ
    rewrite[abs_lt] at fyx
    exact fyx.1
  · apply sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hn)
    intro i hi
    rewrite[mem_range] at hi
    field_simp
    rewrite[show (k:ℝ)*ε = ∑ x ∈ range k, ε by rw[sum_const, card_range, nsmul_eq_mul]]
    rewrite[show (k:ℝ) * f (a + D * ((i:ℝ) + 1)) = ∑ x ∈ range k, f (a + D * ((i:ℝ) + 1)) by rw[sum_const, card_range, nsmul_eq_mul]]
    rewrite[← sum_sub_distrib]
    apply sum_lt_sum_of_nonempty (nonempty_range_iff.mpr hk)
    intro j hj
    rewrite[mem_range] at hj

    have hxab := hxabThm a b D i j k n hi hj hab hk hn hDdef
    have hyab := hyabThm a b D i n hi hab hn hDdef
    have hxyδ := hxyδThm a b D δ i j k n hi hj hab hk hn hDdef hfine
-- 这个不错，不然这 ∀ x，要把 x 写出来，这也太长了
    have fyx := hunif _ hyab _ hxab hxyδ
    rewrite[abs_lt] at fyx
    exact fyx.2


def UnifContOn (f : ℝ → ℝ) (S : Set ℝ) := ∀ ε > 0, ∃ δ > 0, ∀ x ∈ S, ∀ y ∈ S, |y - x| < δ → |f y - f x| < ε

theorem HasIntegral_of_UnifContOn (f : ℝ → ℝ) (a b : ℝ) (hab : a < b) (hf : UnifContOn f (Set.Icc a b)) : IntegrableOn f a b := by
