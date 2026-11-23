import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer.LogConv

variable {B : Type} [CommRing B] {S : Subring B} {ϖ : B} {J : Ideal B}

theorem near_add {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x + y) := by
  obtain ⟨s, hs, h⟩ := hx
  obtain ⟨s', hs', h'⟩ := hy
  refine ⟨s + s', S.add_mem hs hs', ?_⟩
  have := J.add_mem h h'
  convert this using 1; ring

theorem near_sub {m : ℕ} {x y : B} (hx : Near S ϖ J m x) (hy : Near S ϖ J m y) :
    Near S ϖ J m (x - y) := by
  obtain ⟨s, hs, h⟩ := hx
  obtain ⟨s', hs', h'⟩ := hy
  refine ⟨s - s', S.sub_mem hs hs', ?_⟩
  have := J.sub_mem h h'
  convert this using 1; ring

theorem near_mul {a b : ℕ} {x y : B} (hx : Near S ϖ J a x) (hy : Near S ϖ J b y) :
    Near S ϖ J (a + b) (x * y) := by
  obtain ⟨s, hs, h⟩ := hx
  obtain ⟨s', hs', h'⟩ := hy
  refine ⟨s * s', S.mul_mem hs hs', ?_⟩
  have := J.add_mem (J.mul_mem_right y h) (J.mul_mem_left (ϖ ^ a * s) h')
  convert this using 1; ring

theorem near_mono (hϖ : ϖ ∈ S) {a b : ℕ} (hab : a ≤ b) {x : B} (h : Near S ϖ J b x) :
    Near S ϖ J a x := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨ϖ ^ (b - a) * s, S.mul_mem (S.pow_mem hϖ _) hs, ?_⟩
  have e : ϖ ^ a * (ϖ ^ (b - a) * s) = ϖ ^ b * s := by
    rw [← mul_assoc, ← pow_add, Nat.add_sub_cancel' hab]
  rwa [e]

theorem near_of_mem {s : B} (hs : s ∈ S) : Near S ϖ J 0 s := ⟨s, hs, by simp⟩

theorem near_pow {a : ℕ} {x : B} (h : Near S ϖ J a x) (e : ℕ) : Near S ϖ J (a * e) (x ^ e) := by
  induction e with
  | zero => exact ⟨1, S.one_mem, by simp⟩
  | succ e ih =>
    rw [pow_succ, Nat.mul_succ]
    exact near_mul ih h

theorem near_anti {J' : Ideal B} (hJ : J ≤ J') {m : ℕ} {x : B} (h : Near S ϖ J m x) :
    Near S ϖ J' m x := by
  obtain ⟨s, hs, h⟩ := h
  exact ⟨s, hs, hJ h⟩

variable {F : ℕ → Ideal B}

theorem near_all (E : PerEnv S F ϖ) (k : ℕ) {x : B} (h : ∀ m, Near S ϖ (F k) m x) : x ∈ F k := by
  obtain ⟨s, hs, h0⟩ := h 0
  have hs' : s ∈ F k := E.closed k s hs (fun m => by
    obtain ⟨s', hs', h'⟩ := h m
    refine ⟨s', hs', ?_⟩
    have := (F k).sub_mem h' h0
    convert this using 1; ring)
  have := (F k).add_mem h0 hs'
  convert this using 1; ring

theorem near_Qpow (E : PerEnv S F ϖ) {Q : B} (hQ : Q ∈ S) {M : ℕ}
    (h : Near S ϖ (F 1) 1 (Q ^ M)) (k : ℕ) : Near S ϖ (F k) 1 (Q ^ (M * k)) := by
  induction k with
  | zero => exact ⟨0, S.zero_mem, by rw [E.top]; trivial⟩
  | succ k ih =>
    obtain ⟨s, hs, h1⟩ := ih
    obtain ⟨s', hs', h2⟩ := h
    refine ⟨Q ^ (M * k) * s' + s * (Q ^ M - ϖ ^ 1 * s'),
      S.add_mem (S.mul_mem (S.pow_mem hQ _) hs')
        (S.mul_mem hs (S.sub_mem (S.pow_mem hQ _) (S.mul_mem (S.pow_mem E.mem _) hs'))), ?_⟩
    have := E.mul_le k 1 (Ideal.mul_mem_mul h1 h2)
    convert this using 1; ring

theorem iter_succ (ϖ : B) (q n : ℕ) (x : B) :
    ltIter ϖ q (n + 1) x = ϖ * ltIter ϖ q n x + ltIter ϖ q n x ^ q := by
  unfold ltIter
  rw [Function.iterate_succ_apply']

theorem iter_mem (hϖ : ϖ ∈ S) {Q : B} (hQ : Q ∈ S) (q n : ℕ) : ltIter ϖ q n Q ∈ S := by
  induction n with
  | zero => simpa [ltIter] using hQ
  | succ n ih =>
    rw [iter_succ]
    exact S.add_mem (S.mul_mem hϖ ih) (S.pow_mem ih _)

theorem pow_congr' {y z : B} (hy : y ∈ S) (hz : z ∈ S) (h : ∃ s ∈ S, y - z = ϖ * s) (e : ℕ) :
    ∃ s ∈ S, y ^ e - z ^ e = ϖ * s := by
  induction e with
  | zero => exact ⟨0, S.zero_mem, by simp⟩
  | succ e ih =>
    obtain ⟨s, hs, hh⟩ := h
    obtain ⟨u, hu, ih⟩ := ih
    refine ⟨y ^ e * s + u * z, S.add_mem (S.mul_mem (S.pow_mem hy _) hs) (S.mul_mem hu hz), ?_⟩
    linear_combination (y ^ e) * hh + z * ih

theorem iter_congr (hϖ : ϖ ∈ S) {Q : B} (hQ : Q ∈ S) (q n : ℕ) :
    ∃ s ∈ S, ltIter ϖ q n Q - Q ^ (q ^ n) = ϖ * s := by
  induction n with
  | zero => exact ⟨0, S.zero_mem, by simp [ltIter]⟩
  | succ n ih =>
    have hy := iter_mem hϖ hQ q n
    obtain ⟨u, hu, h2⟩ := pow_congr' hy (S.pow_mem hQ (q ^ n)) ih q
    refine ⟨ltIter ϖ q n Q + u, S.add_mem hy hu, ?_⟩
    rw [iter_succ, pow_succ q n, pow_mul]
    linear_combination h2

theorem near_iter (E : PerEnv S F ϖ) {q : ℕ} (hq : 2 ≤ q) {Q : B} (hQ : Q ∈ S) {M : ℕ}
    (h : Near S ϖ (F 1) 1 (Q ^ M)) (k : ℕ) : Near S ϖ (F k) 1 (ltIter ϖ q (M * k) Q) := by
  have hL : M * k ≤ q ^ (M * k) := (Nat.lt_pow_self hq).le
  obtain ⟨s, hs, hy⟩ := iter_congr E.mem hQ q (M * k)
  have e : Q ^ (q ^ (M * k)) = Q ^ (M * k) * Q ^ (q ^ (M * k) - M * k) := by
    rw [← pow_add, Nat.add_sub_cancel' hL]
  have h1 : Near S ϖ (F k) 1 (Q ^ (q ^ (M * k))) := by
    rw [e]
    exact near_mul (near_Qpow E hQ h k) (near_of_mem (S.pow_mem hQ _))
  obtain ⟨s1, hs1, h1'⟩ := h1
  refine ⟨s1 + s, S.add_mem hs1 hs, ?_⟩
  convert h1' using 1
  linear_combination hy

theorem near_step (hϖ : ϖ ∈ S) {q : ℕ} (hq : 2 ≤ q) {b : ℕ} (hb : 1 ≤ b) {y : B}
    (h : Near S ϖ J b y) : Near S ϖ J (b + 1) (ϖ * y + y ^ q) := by
  have h0 : Near S ϖ J 1 ϖ := ⟨1, S.one_mem, by simp⟩
  have h1 : Near S ϖ J (b + 1) (ϖ * y) := by
    rw [add_comm]; exact near_mul h0 h
  have h2 : Near S ϖ J (b + 1) (y ^ q) :=
    near_mono hϖ (by nlinarith) (near_pow h q)
  exact near_add h1 h2

theorem near_iter_add (E : PerEnv S F ϖ) {q : ℕ} (hq : 2 ≤ q) {Q : B} {k n0 : ℕ}
    (h : Near S ϖ (F k) 1 (ltIter ϖ q n0 Q)) (j : ℕ) :
    Near S ϖ (F k) (1 + j) (ltIter ϖ q (n0 + j) Q) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    rw [show n0 + (j + 1) = n0 + j + 1 from rfl, iter_succ]
    exact near_step (b := 1 + j) E.mem hq (by omega) ih

theorem iter_diff {ϖ' : B} (hu : ϖ * ϖ' = 1) (q n : ℕ) (Q : B) :
    ϖ' ^ (n + 1) * ltIter ϖ q (n + 1) Q - ϖ' ^ n * ltIter ϖ q n Q =
      ϖ' ^ (n + 1) * ltIter ϖ q n Q ^ q := by
  rw [iter_succ]
  linear_combination (ϖ' ^ n * ltIter ϖ q n Q) * hu

theorem near_diff (E : PerEnv S F ϖ) {ϖ' : B} (hu : ϖ * ϖ' = 1) {q : ℕ} (hq : 2 ≤ q) {Q : B}
    {k n0 : ℕ} (h : Near S ϖ (F k) 1 (ltIter ϖ q n0 Q)) (j : ℕ) :
    Near S ϖ (F k) (1 + j) (ϖ ^ n0 * (ϖ' ^ (n0 + j + 1) * ltIter ϖ q (n0 + j + 1) Q -
      ϖ' ^ (n0 + j) * ltIter ϖ q (n0 + j) Q)) := by
  have h1 : Near S ϖ (F k) (2 * j + 2) (ltIter ϖ q (n0 + j) Q ^ q) :=
    near_mono E.mem (by nlinarith) (near_pow (near_iter_add E hq h j) q)
  obtain ⟨s, hs, hf⟩ := h1
  refine ⟨s, hs, ?_⟩
  have hU : ϖ ^ (n0 + j + 1) * ϖ' ^ (n0 + j + 1) = 1 := by rw [← mul_pow, hu, one_pow]
  have e : ϖ ^ n0 * (ϖ' ^ (n0 + j + 1) * ltIter ϖ q (n0 + j + 1) Q -
      ϖ' ^ (n0 + j) * ltIter ϖ q (n0 + j) Q) - ϖ ^ (1 + j) * s =
      (ϖ ^ n0 * ϖ' ^ (n0 + j + 1)) * (ltIter ϖ q (n0 + j) Q ^ q - ϖ ^ (2 * j + 2) * s) := by
    rw [iter_diff hu]
    linear_combination (ϖ ^ (1 + j) * s) * hU
  rw [e]
  exact (F k).mul_mem_left _ hf

theorem level_limit (E : PerEnv S F ϖ) {ϖ' : B} (hu : ϖ * ϖ' = 1) (x : ℕ → B) {k : ℕ} (c n0 : ℕ)
    (h : ∀ j, Near S ϖ (F k) (1 + j) (ϖ ^ c * (x (n0 + j + 1) - x (n0 + j)))) :
    ∃ t, ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t)) := by
  choose s hs hf using h
  obtain ⟨r, hr, hsum⟩ := E.sumS s hs
  have tel : ∀ J, ϖ ^ c * (x (n0 + J) - x n0) -
      ∑ i ∈ Finset.range J, ϖ ^ (1 + i) * s i ∈ F k := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      have := (F k).add_mem ih (hf J)
      rw [Finset.sum_range_succ, show n0 + (J + 1) = n0 + J + 1 from rfl]
      convert this using 1; ring
  have hc : ϖ ^ c * ϖ' ^ c = 1 := by rw [← mul_pow, hu, one_pow]
  refine ⟨x n0 + ϖ' ^ c * (ϖ * r), fun m => ⟨n0 + m, fun n hn => ?_⟩⟩
  obtain ⟨J, rfl⟩ : ∃ J, n = n0 + J := ⟨n - n0, by omega⟩
  have hJ : m ≤ J + 1 := by omega
  obtain ⟨a, ha, hae⟩ := hsum J
  refine near_mono E.mem hJ ⟨-a, S.neg_mem ha, ?_⟩
  have hmul : ∑ i ∈ Finset.range J, ϖ ^ (1 + i) * s i =
      ϖ * ∑ i ∈ Finset.range J, ϖ ^ i * s i := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e : ϖ ^ c * (x (n0 + J) - (x n0 + ϖ' ^ c * (ϖ * r))) - ϖ ^ (J + 1) * (-a) =
      ϖ ^ c * (x (n0 + J) - x n0) - ∑ i ∈ Finset.range J, ϖ ^ (1 + i) * s i := by
    rw [hmul]
    linear_combination (-(ϖ * r)) * hc - ϖ * hae
  rw [e]
  exact tel J

theorem glue (E : PerEnv S F ϖ) {ϖ' : B} (hu : ϖ * ϖ' = 1) (x : ℕ → B)
    (h : ∀ k, ∃ (c : ℕ) (t : B), ∀ m, ∃ N, ∀ n ≥ N, Near S ϖ (F k) m (ϖ ^ c * (x n - t))) :
    ∃ t, Tends S F ϖ x t := by
  choose c t h using h
  have key : ∀ k, t (k + 1) - t k ∈ F k := fun k => by
    have hall : ∀ m, Near S ϖ (F k) m (ϖ ^ (c k + c (k + 1)) * (t (k + 1) - t k)) := fun m => by
      obtain ⟨N1, h1⟩ := h k m
      obtain ⟨N2, h2⟩ := h (k + 1) m
      have a1 := h1 (max N1 N2) (le_max_left _ _)
      have a2 := near_anti (E.anti k) (h2 (max N1 N2) (le_max_right _ _))
      have b1 := near_mul (near_of_mem (S.pow_mem E.mem (c (k + 1)))) a1
      have b2 := near_mul (near_of_mem (S.pow_mem E.mem (c k))) a2
      have b := near_sub b1 b2
      rw [zero_add] at b
      convert b using 1; ring
    have := (F k).mul_mem_left (ϖ' ^ (c k + c (k + 1))) (near_all E k hall)
    convert this using 1
    rw [← mul_assoc, ← mul_pow, mul_comm ϖ', hu, one_pow, one_mul]
  obtain ⟨T, hT⟩ := E.complete t key
  refine ⟨T, fun k => ⟨c k, fun m => ?_⟩⟩
  obtain ⟨N, hN⟩ := h k m
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨s, hs, hf⟩ := hN n hn
  refine ⟨s, hs, ?_⟩
  have := (F k).sub_mem hf ((F k).mul_mem_left (ϖ ^ c k) (hT k))
  convert this using 1; ring

theorem log_converges : ∀ {B : Type} [CommRing B] {S : Subring B} {F : ℕ → Ideal B} {ϖ : B}, PerEnv S F ϖ → ∀ (ϖ' : B), ϖ * ϖ' = 1 → ∀ (q : ℕ), 2 ≤ q →
    ∀ Q ∈ S, (∃ M : ℕ, 0 < M ∧ Near S ϖ (F 1) 1 (Q ^ M)) →
      ∃ t, Tends S F ϖ (fun n => ϖ' ^ n * ltIter ϖ q n Q) t := by
  rintro B _ S F ϖ E ϖ' hu q hq Q hQ ⟨M, -, hN⟩
  refine glue E hu _ fun k => ?_
  obtain ⟨t, ht⟩ := level_limit E hu (fun n => ϖ' ^ n * ltIter ϖ q n Q) (M * k) (M * k)
    (near_diff E hu hq (near_iter E hq hQ hN k))
  exact ⟨M * k, t, ht⟩

end GlobalTheory.CompanionTheory.LTPer.LogConv
