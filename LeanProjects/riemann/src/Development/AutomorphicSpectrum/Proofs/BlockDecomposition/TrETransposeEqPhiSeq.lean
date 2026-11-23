import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsMultOfFintype

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.WaveMult.GlTranspose

variable {n : ℕ} {A : Type} [Ring A]

theorem epw_zero (e : Fin n → Fin n → A) (a b : Fin n) :
    Epw e 0 a b = if a = b then 1 else 0 := by
  rw [Epw]

theorem epw_succ (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, e a c * Epw e m c b := by
  rw [Epw]

theorem epw_succ_right (e : Fin n → Fin n → A) (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) a b = ∑ c, Epw e m a c * e c b := by
  induction m generalizing a b with
  | zero =>
    simp [epw_succ, epw_zero]
  | succ m ih =>
    calc Epw e (m + 1 + 1) a b = ∑ c, e a c * ∑ d, Epw e m c d * e d b := by
          rw [epw_succ]
          exact sum_congr rfl fun c _ => by rw [ih]
      _ = ∑ d, (∑ c, e a c * Epw e m c d) * e d b := by
          simp only [mul_sum, sum_mul, mul_assoc]
          exact Finset.sum_comm
      _ = ∑ c, Epw e (m + 1) a c * e c b := sum_congr rfl fun d _ => by rw [epw_succ]

theorem bco_zero_zero (N : A) (τ : ℕ → A) : bco N τ 0 0 = 1 := by rw [bco]

theorem bco_zero_succ (N : A) (τ : ℕ → A) (j : ℕ) : bco N τ 0 (j + 1) = 0 := by rw [bco]

theorem bco_succ_zero (N : A) (τ : ℕ → A) (m : ℕ) :
    bco N τ (m + 1) 0 = N * bco N τ m 0 - τ m := by rw [bco]

theorem bco_succ_succ (N : A) (τ : ℕ → A) (m j : ℕ) :
    bco N τ (m + 1) (j + 1) = bco N τ m j + N * bco N τ m (j + 1) := by rw [bco]

theorem bco_eq_zero (N : A) (τ : ℕ → A) (m j : ℕ) (h : m < j) : bco N τ m j = 0 := by
  induction m generalizing j with
  | zero =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    exact bco_zero_succ N τ j
  | succ m ih =>
    obtain ⟨j, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    rw [bco_succ_succ, ih j (by omega), ih (j + 1) (by omega)]
    simp

theorem bco_self (N : A) (τ : ℕ → A) (m : ℕ) : bco N τ m m = 1 := by
  induction m with
  | zero => exact bco_zero_zero N τ
  | succ m ih =>
    rw [bco_succ_succ, ih, bco_eq_zero N τ m (m + 1) (by omega)]
    simp

theorem phiSeq_eq (N : A) (τ : ℕ → A) (m : ℕ) :
    phiSeq N τ m = τ m - ∑ j ∈ range m, bco N τ m j * phiSeq N τ j := by
  rw [phiSeq, Fin.sum_univ_eq_sum_range (fun j => bco N τ m j * phiSeq N τ j) m]

section Gl

variable (e : Fin n → Fin n → A)
  (he : ∀ a b c d, e a b * e c d - e c d * e a b =
    (if b = c then e a d else 0) - (if a = d then e c b else 0))
include he

theorem comm_epw (m : ℕ) (a b c d : Fin n) :
    e a b * Epw e m c d - Epw e m c d * e a b =
      (if b = c then Epw e m a d else 0) - (if a = d then Epw e m c b else 0) := by
  induction m generalizing c d with
  | zero =>
    simp only [epw_zero]
    by_cases h1 : c = d
    · subst h1
      by_cases h2 : b = c
      · subst h2; simp
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h2, h3]
    · by_cases h2 : b = c
      · subst h2
        by_cases h3 : a = d
        · subst h3; simp [h1]
        · simp [h1, h3]
      · have h3 : ¬ c = b := fun h => h2 h.symm
        simp [h1, h2, h3]
  | succ m ih =>
    have step : ∀ f, e a b * (e c f * Epw e m f d) - (e c f * Epw e m f d) * e a b =
        ((if b = c then e a f else 0) - (if a = f then e c b else 0)) * Epw e m f d +
          e c f * ((if b = f then Epw e m a d else 0) - (if a = d then Epw e m f b else 0)) := by
      intro f
      rw [← he a b c f, ← ih f d]
      noncomm_ring
    rw [epw_succ e m c d, mul_sum, sum_mul, ← sum_sub_distrib, sum_congr rfl (fun f _ => step f)]
    simp only [sub_mul, mul_sub, sum_add_distrib, sum_sub_distrib, ite_mul, mul_ite, zero_mul,
      mul_zero, sum_ite_eq, sum_ite_eq', mem_univ, if_true]
    by_cases h1 : b = c <;> by_cases h2 : a = d <;>
      simp only [h1, h2, if_true, if_false, ← epw_succ, sum_const_zero] <;> abel

theorem transpose_step (m : ℕ) (a b : Fin n) :
    Epw e (m + 1) b a =
      ∑ c, Epw e m c a * e b c + (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
  have h : Epw e (m + 1) b a - ∑ c, Epw e m c a * e b c =
      (n : A) * Epw e m b a - (if a = b then trE e m else 0) := by
    rw [epw_succ, ← sum_sub_distrib,
      sum_congr rfl (fun c _ => comm_epw e he m b c c a), sum_sub_distrib]
    by_cases h1 : a = b
    · subst h1; simp [trE]
    · have h2 : ¬ b = a := fun h => h1 h.symm
      simp [h1, h2]
  rw [add_sub_assoc, ← h]
  abel

theorem transpose_poly (m : ℕ) (a b : Fin n) :
    Epw e m b a =
      ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * Epw (fun a b => e b a) j a b := by
  induction m generalizing a b with
  | zero =>
    simp only [zero_add, range_one, sum_singleton, bco_zero_zero, one_mul, epw_zero]
    simp only [eq_comm]
  | succ m ih =>
    set f : Fin n → Fin n → A := fun a b => e b a with hf
    set N : A := (n : A) with hN
    set τ : ℕ → A := trE e with hτ
    have key : ∑ c, Epw e m c a * e b c =
        ∑ j ∈ range (m + 1), bco N τ m j * Epw f (j + 1) a b := by
      simp only [epw_succ_right f, mul_sum]
      rw [sum_comm]
      refine sum_congr rfl fun c _ => ?_
      rw [ih a c, sum_mul]
      refine sum_congr rfl fun j _ => ?_
      rw [mul_assoc]
    have hn : N * Epw e m b a =
        ∑ j ∈ range (m + 1), N * bco N τ m (j + 1) * Epw f (j + 1) a b +
          N * bco N τ m 0 * Epw f 0 a b := by
      rw [← sum_range_succ' (fun j => N * bco N τ m j * Epw f j a b) (m + 1),
        sum_range_succ _ (m + 1), bco_eq_zero N τ m (m + 1) (by omega), ih a b, mul_sum]
      simp [mul_assoc]
    rw [transpose_step e he, key, hn, sum_range_succ' _ (m + 1), bco_succ_zero]
    simp only [bco_succ_succ, add_mul, sum_add_distrib, sub_mul, epw_zero f]
    by_cases h1 : a = b
    · simp [h1]
      try abel
    · simp [h1]
      try abel

theorem trE_eq_sum (m : ℕ) :
    trE e m = ∑ j ∈ range (m + 1), bco (n : A) (trE e) m j * trE (fun a b => e b a) j := by
  have h : trE e m = ∑ a, Epw e m a a := rfl
  rw [h, sum_congr rfl (fun a _ => transpose_poly e he m a a), sum_comm]
  refine sum_congr rfl fun j _ => ?_
  rw [trE, mul_sum]

end Gl

theorem trE_transpose_eq_phiSeq (n : ℕ) {A : Type} [Ring A] [Algebra ℂ A]
    (e : Fin n → Fin n → A)
    (he : ∀ a b c d, e a b * e c d - e c d * e a b =
      (if b = c then e a d else 0) - (if a = d then e c b else 0)) (m : ℕ) :
    trE (fun a b => e b a) m = phiSeq (n : A) (trE e) m := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    have h := trE_eq_sum e he m
    rw [sum_range_succ, bco_self, one_mul] at h
    have hs : ∑ j ∈ range m, bco (n : A) (trE e) m j * phiSeq (n : A) (trE e) j =
        ∑ j ∈ range m, bco (n : A) (trE e) m j * trE (fun a b => e b a) j :=
      sum_congr rfl fun j hj => by rw [ih j (mem_range.mp hj)]
    rw [phiSeq_eq, hs, h, add_sub_cancel_left]

end GlobalTheory.CompanionTheory.WaveMult.GlTranspose
