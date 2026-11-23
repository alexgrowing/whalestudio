import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.IsFirstChernClassOfLineBundle
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.DatPull
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb GroundTheory.PAdicHodge
namespace GlobalTheory.CompanionTheory.TruncLog

variable {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J)

theorem mul_dpow_eq_succ {x : A} (hx : x ∈ J) (a : ℕ) :
    x * δ.dpow a x = ((a : A) + 1) * δ.dpow (a + 1) x := by
  have h := δ.mul_dpow (m := 1) (n := a) hx
  rw [δ.dpow_one hx] at h
  rw [h, Nat.choose_one_right, add_comm 1 a]
  push_cast
  ring

theorem factorial_mul_dpow_eq_zero {N : ℕ} {x : A}
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) {a k : ℕ} (ha : N < a)
    (hk : a ≤ k + 1) : (k.factorial : A) * δ.dpow a x = 0 := by
  obtain ⟨c, rfl⟩ : ∃ c, a = c + 1 := ⟨a - 1, by omega⟩
  obtain ⟨d, hd⟩ := Nat.factorial_dvd_factorial (show c ≤ k by omega)
  rw [hd]
  push_cast
  rw [mul_comm (c.factorial : A), mul_assoc, hN c (by omega), mul_zero]

theorem one_add_mul_sum_succ {x : A} (hx : x ∈ J) (m n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + (m + 1)).factorial : A) * δ.dpow a x =
      ((m : A) + 1) * ∑ a ∈ Finset.range (n + 1),
        (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x
      + (-1) ^ n * ((n + (m + 1)).factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    have e : (((m + 1).factorial : ℕ) : A) = ((m : A) + 1) * (m.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, e, Nat.cast_zero]
    ring
  | succ n ih =>
    have e1 : ((n + 1 + (m + 1)).factorial : A)
        = ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + (m + 1) = (n + (m + 1)) + 1 by omega, Nat.factorial_succ]
      push_cast; ring
    have e2 : ((n + 1 + m).factorial : A) = ((n + (m + 1)).factorial : A) := by
      rw [show n + 1 + m = n + (m + 1) by omega]
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, Finset.sum_range_succ _ (n + 1), e1, e2]
    push_cast at hxp ⊢
    linear_combination
      (-1 : A) ^ (n + 1) * ((n : A) + m + 2) * ((n + (m + 1)).factorial : A) * hxp

theorem one_add_mul_sum_zero {x : A} (hx : x ∈ J) (n : ℕ) :
    (1 + x) * ∑ a ∈ Finset.range (n + 1), (-1 : A) ^ a * (a.factorial : A) * δ.dpow a x =
      1 + (-1) ^ n * (n.factorial : A) * ((n : A) + 1) * δ.dpow (n + 1) x := by
  induction n with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, δ.dpow_zero hx, δ.dpow_one hx,
      mul_one, Nat.factorial_zero, Nat.cast_one, Nat.cast_zero]
  | succ n ih =>
    have e1 : ((n + 1).factorial : A) = ((n : A) + 1) * (n.factorial : A) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hxp := mul_dpow_eq_succ δ hx (n + 1)
    rw [Finset.sum_range_succ, mul_add, ih, e1]
    push_cast at hxp ⊢
    linear_combination (-1 : A) ^ (n + 1) * ((n : A) + 1) * (n.factorial : A) * hxp

theorem one_add_pow_mul_sum {N : ℕ} {x : A} (hx : x ∈ J)
    (hN : ∀ k, N ≤ k → (k.factorial : A) * δ.dpow (k + 1) x = 0) (m : ℕ) :
    (1 + x) ^ (m + 1) * ∑ a ∈ Finset.range (N + 1),
      (-1 : A) ^ a * ((a + m).factorial : A) * δ.dpow a x = (m.factorial : A) := by
  induction m with
  | zero =>
    simp only [zero_add, pow_one, add_zero, Nat.factorial_zero, Nat.cast_one]
    rw [one_add_mul_sum_zero δ hx N]
    have := hN N le_rfl
    linear_combination ((-1 : A) ^ N * ((N : A) + 1)) * this
  | succ m ih =>
    have z := factorial_mul_dpow_eq_zero δ hN (a := N + 1) (k := N + (m + 1)) (by omega) (by omega)
    rw [pow_succ, mul_assoc, one_add_mul_sum_succ δ hx m N, Nat.factorial_succ]
    push_cast
    linear_combination ((m : A) + 1) * ih
      + (1 + x) ^ (m + 1) * (-1 : A) ^ N * ((N : A) + 1) * z

theorem sum_antidiagonal_eq_sum_box (g : ℕ → ℕ → A) {N M : ℕ} (hM : 2 * N ≤ M)
    (hg : ∀ a b, N < a ∨ N < b → g a b = 0) :
    ∑ k ∈ Finset.range (M + 1), ∑ p ∈ Finset.HasAntidiagonal.antidiagonal k, g p.1 p.2 =
      ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b := by
  rw [← Finset.sum_product' (f := g),
    ← Finset.sum_fiberwise_of_maps_to
      (s := Finset.range (N + 1) ×ˢ Finset.range (N + 1)) (t := Finset.range (M + 1))
      (g := fun p => p.1 + p.2)
      (by intro p hp; simp only [Finset.mem_product, Finset.mem_range] at hp ⊢; omega)]
  refine Finset.sum_congr rfl fun k _ => ?_
  symm
  apply Finset.sum_subset
  · intro p hp
    simp only [Finset.mem_filter] at hp
    simpa using hp.2
  · intro p hp hp'
    simp only [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, not_and] at hp'
    apply hg
    by_contra hc
    exact hp' (by omega) hp

theorem dlog_mul {A : Type} [CommRing A] {J : Ideal A} (δ : DividedPowers J) (N : ℕ)
    (h : ∀ k, N ≤ k → ∀ x ∈ J, (k.factorial : A) * δ.dpow (k + 1) x = 0) (v w : A)
    (hv : v - 1 ∈ J) (hw : w - 1 ∈ J) :
    B.dlog δ N (v * w) = B.dlog δ N v + B.dlog δ N w := by
  obtain ⟨x, rfl⟩ : ∃ x, v = 1 + x := ⟨v - 1, by ring⟩
  obtain ⟨y, rfl⟩ : ∃ y, w = 1 + y := ⟨w - 1, by ring⟩
  have hx : x ∈ J := by simpa using hv
  have hy : y ∈ J := by simpa using hw
  have hvy : (1 + x) * y ∈ J := J.mul_mem_left _ hy
  have hz : x + (1 + x) * y ∈ J := J.add_mem hx hvy
  have dl : ∀ t : A, B.dlog δ N (1 + t) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) t := by
    intro t; simp [B.dlog]
  have dz : B.dlog δ N ((1 + x) * (1 + y)) =
      ∑ k ∈ Finset.range N, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    have : (1 + x) * (1 + y) = 1 + (x + (1 + x) * y) := by ring
    rw [this, dl]
  let g : ℕ → ℕ → A := fun a b => (-1 : A) ^ (a + b + 1) * ((a + b - 1).factorial : A) *
    δ.dpow a x * ((1 + x) ^ b * δ.dpow b y)
  have hg : ∀ a b, N < a ∨ N < b → g a b = 0 := by
    intro a b hab
    rcases hab with hab | hab
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk x hx) (a := a) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      rw [mul_assoc ((-1 : A) ^ (a + b + 1)), this]
      ring
    · have := factorial_mul_dpow_eq_zero δ (fun k hk => h k hk y hy) (a := b) (k := a + b - 1)
        hab (by omega)
      simp only [g]
      linear_combination
        ((-1 : A) ^ (a + b + 1) * δ.dpow a x * (1 + x) ^ b) * this
  have s1 : B.dlog δ N ((1 + x) * (1 + y)) = ∑ k ∈ Finset.range (2 * N),
      (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) := by
    rw [dz]
    apply Finset.sum_subset
    · intro k hk; simp only [Finset.mem_range] at hk ⊢; omega
    · intro k _ hk
      simp only [Finset.mem_range, not_lt] at hk
      rw [mul_assoc, h k hk _ hz, mul_zero]
  have s2 : ∀ k, (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) (x + (1 + x) * y) =
      ∑ p ∈ Finset.HasAntidiagonal.antidiagonal (k + 1), g p.1 p.2 := by
    intro k
    rw [δ.dpow_add hx hvy, Finset.mul_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p.1 + p.2 = k + 1 := by simpa using hp
    simp only [g]
    rw [hp', δ.dpow_mul hy, show k + 1 - 1 = k by omega]
    ring
  have s3 := sum_antidiagonal_eq_sum_box g (N := N) (M := 2 * N) le_rfl hg
  rw [Finset.sum_range_succ'] at s3
  have s4 : ∑ a ∈ Finset.range (N + 1), ∑ b ∈ Finset.range (N + 1), g a b =
      g 0 0 + (B.dlog δ N (1 + x) + B.dlog δ N (1 + y)) := by
    rw [Finset.sum_comm, Finset.sum_range_succ', Finset.sum_range_succ' (fun a => g a 0), dl, dl]
    have t1 : ∀ k, g (k + 1) 0 = (-1 : A) ^ k * (k.factorial : A) * δ.dpow (k + 1) x := by
      intro k
      simp only [g, add_zero, pow_zero, δ.dpow_zero hy, show k + 1 - 1 = k by omega]
      ring
    have t2 : ∀ b, ∑ a ∈ Finset.range (N + 1), g a (b + 1) =
        (-1 : A) ^ b * (b.factorial : A) * δ.dpow (b + 1) y := by
      intro b
      rw [← one_add_pow_mul_sum δ hx (fun k hk => h k hk x hx) b]
      simp only [g]
      rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [show a + (b + 1) - 1 = a + b by omega]
      ring
    simp only [t1, t2]
    ring
  have s5 : ∑ p ∈ Finset.HasAntidiagonal.antidiagonal 0, g p.1 p.2 = g 0 0 := by simp
  rw [s5, s4] at s3
  simp only [← s2] at s3
  rw [s1]
  linear_combination s3

end GlobalTheory.CompanionTheory.TruncLog
