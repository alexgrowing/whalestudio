import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WBMemLatS
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum

theorem adic_sum_exists {W : Type} [CommRing W] (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (N : ℕ) (hN : 0 < N) (b : ℕ → W) :
    ∃ L : W, ∀ M, ∃ c : W,
      L - ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n = (p : W) ^ (M / N) * c := by
  set I : Ideal W := Ideal.span {(p : W)} with hI
  set g : ℕ → W := fun M => ∑ n ∈ Finset.range M, (p : W) ^ (n / N) * b n with hg
  have key : ∀ e M₁ M₂, e * N ≤ M₁ → M₁ ≤ M₂ → g M₂ - g M₁ ∈ I ^ e := by
    intro e M₁ M₂ h₁ h₂
    simp only [hg]
    rw [← Finset.sum_Ico_eq_sub _ h₂]
    refine Ideal.sum_mem _ fun n hn => ?_
    have hn' : e ≤ n / N := (Nat.le_div_iff_mul_le hN).2 (h₁.trans (Finset.mem_Ico.1 hn).1)
    exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right hn'
      (Ideal.pow_mem_pow (Ideal.mem_span_singleton_self _) _))
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := I) (M := W) inferInstance
    (f := fun k => g (k * N)) (by
      intro m n hmn
      rw [SModEq.sub_mem]
      simp only [smul_eq_mul, Ideal.mul_top]
      have := key m (m * N) (n * N) le_rfl (Nat.mul_le_mul_right N hmn)
      have h2 := (I ^ m).neg_mem this
      simpa using h2)
  refine ⟨L, fun M => ?_⟩
  have h₁ : L - g (M / N * N) ∈ I ^ (M / N) := by
    have := hL (M / N)
    rw [SModEq.sub_mem] at this
    simp only [smul_eq_mul, Ideal.mul_top] at this
    have h2 := (I ^ (M / N)).neg_mem this
    simpa using h2
  have h₂ : g M - g (M / N * N) ∈ I ^ (M / N) := key _ _ _ le_rfl (Nat.div_mul_le_self M N)
  have h₃ : L - g M ∈ I ^ (M / N) := by
    have := (I ^ (M / N)).sub_mem h₁ h₂
    simpa using this
  rw [hI, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at h₃
  obtain ⟨c, hc⟩ := h₃
  exact ⟨c, by rw [mul_comm, hc]⟩

theorem sum_exists {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B)
    (hw : ∀ a, w a ∈ S) (hT : ∀ t ∈ T, t ∈ S)
    (hgen : ∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t))
    (ϖ y : B) (N : ℕ) (hN : 0 < N) (hϖ : ϖ ∈ S) (hy : y ∈ S) (hN' : ϖ ^ N = (p : B) * y)
    (s : ℕ → B) (hs : ∀ n, s n ∈ S) :
    ∃ r ∈ S, ∀ M, ∃ c ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = (p : B) ^ (M / N) * c := by
  have hu : ∀ n, ϖ ^ (n % N) * y ^ (n / N) * s n ∈ S := fun n =>
    S.mul_mem (S.mul_mem (S.pow_mem hϖ _) (S.pow_mem hy _)) (hs n)
  choose a ha using fun n => hgen _ (hu n)
  have hpow : ∀ n, ϖ ^ n * s n = (p : B) ^ (n / N) * ∑ t ∈ T, t * w (a n t) := by
    intro n
    rw [← ha n]
    have hϖn : ϖ ^ n = ((p : B) ^ (n / N) * y ^ (n / N)) * ϖ ^ (n % N) := by
      have h0 : ϖ ^ n = ϖ ^ (N * (n / N) + n % N) := by rw [Nat.div_add_mod]
      rw [h0, pow_add, pow_mul, hN', mul_pow]
    rw [hϖn]
    ring
  choose α hα using fun t => adic_sum_exists (W := W) p N hN (fun n => a n t)
  choose c hc using fun t M => hα t M
  refine ⟨∑ t ∈ T, t * w (α t), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), fun M => ?_⟩
  refine ⟨∑ t ∈ T, t * w (c t M), S.sum_mem fun t ht => S.mul_mem (hT t ht) (hw _), ?_⟩
  have hterm : ∀ t, w (α t) = ∑ n ∈ Finset.range M, (p : B) ^ (n / N) * w (a n t)
      + (p : B) ^ (M / N) * w (c t M) := by
    intro t
    have h := congrArg w (hc t M)
    simp only [map_sub, map_sum, map_mul, map_pow, map_natCast] at h
    rw [← h]; ring
  simp only [hpow, hterm, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  have hswap : ∑ n ∈ Finset.range M, ∑ t ∈ T, (p : B) ^ (n / N) * (t * w (a n t))
      = ∑ t ∈ T, ∑ n ∈ Finset.range M, t * ((p : B) ^ (n / N) * w (a n t)) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun n _ => by ring
  rw [hswap, add_sub_cancel_left]
  exact Finset.sum_congr rfl fun t _ => by ring

theorem sum_with_tails {W B : Type} [CommRing W] [CommRing B] (w : W →+* B) (p : ℕ)
    [IsAdicComplete (Ideal.span {(p : W)}) W] (S : Subring B) (T : Finset B) :
    (∀ a, w a ∈ S) → (∀ t ∈ T, t ∈ S) → (∀ s ∈ S, ∃ a : B → W, s = ∑ t ∈ T, t * w (a t)) →
    (∀ x, (∀ m : ℕ, ∃ s ∈ S, x = (p : B) ^ m * s) → x = 0) →
    ∀ (ϖ y : B) (N : ℕ), 0 < N → ϖ ∈ S → y ∈ S → ϖ ^ N = (p : B) * y →
    ∀ s : ℕ → B, (∀ n, s n ∈ S) → ∃ r ∈ S, ∀ M, ∃ a ∈ S,
      r - ∑ n ∈ Finset.range M, ϖ ^ n * s n = ϖ ^ M * a := by
  intro hw hT hgen hsep ϖ y N hN hϖ hy hN' s hs
  obtain ⟨r, hrS, hr⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN' s hs
  refine ⟨r, hrS, fun M => ?_⟩
  obtain ⟨rM, hrMS, hrM⟩ := sum_exists w p S T hw hT hgen ϖ y N hN hϖ hy hN'
    (fun n => s (M + n)) (fun n => hs _)
  refine ⟨rM, hrMS, ?_⟩
  have hd : r - ∑ n ∈ Finset.range M, ϖ ^ n * s n - ϖ ^ M * rM = 0 := by
    refine hsep _ fun m => ?_
    obtain ⟨c₁, hc₁S, hc₁⟩ := hr (M + N * m)
    obtain ⟨c₂, hc₂S, hc₂⟩ := hrM (N * m)
    have hdiv₁ : (M + N * m) / N = M / N + m := Nat.add_mul_div_left _ _ hN
    have hdiv₂ : (N * m) / N = m := Nat.mul_div_cancel_left _ hN
    rw [hdiv₁] at hc₁
    rw [hdiv₂] at hc₂
    refine ⟨(p : B) ^ (M / N) * c₁ - ϖ ^ M * c₂,
      S.sub_mem (S.mul_mem (S.pow_mem (natCast_mem S p) _) hc₁S)
        (S.mul_mem (S.pow_mem hϖ _) hc₂S), ?_⟩
    rw [Finset.sum_range_add] at hc₁
    have e₁ : r = ∑ n ∈ Finset.range M, ϖ ^ n * s n
        + ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        + (p : B) ^ (M / N + m) * c₁ := by rw [← hc₁]; ring
    have e₂ : rM = ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) + (p : B) ^ m * c₂ := by
      rw [← hc₂]; ring
    have e₃ : ∑ n ∈ Finset.range (N * m), ϖ ^ (M + n) * s (M + n)
        = ϖ ^ M * ∑ n ∈ Finset.range (N * m), ϖ ^ n * s (M + n) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [e₁, e₂, e₃]
    ring
  exact sub_eq_zero.1 hd

end GlobalTheory.CompanionTheory.LTPer.PowerSeriesSum
