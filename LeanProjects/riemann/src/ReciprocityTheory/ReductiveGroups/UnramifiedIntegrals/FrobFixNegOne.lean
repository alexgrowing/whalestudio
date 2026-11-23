import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.KurDefs

noncomputable section

namespace ReciprocityTheory.ChartRestriction.L1

open Formalism.L2.Th1.CM

section General

variable {R : Type*} [CommRing R] (p : ℕ)

def FrobFix (x : R) : Prop := ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x

variable {p}

theorem frobFix_iter {x : R} {f : ℕ} (h : (p : R) ∣ x ^ (p ^ f) - x) (k : ℕ) :
    (p : R) ∣ x ^ (p ^ (f * (k + 1))) - x := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have e : x ^ (p ^ (f * (k + 1 + 1))) = (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) := by
      rw [← pow_mul, ← pow_add]
      congr 2
    rw [e]
    have h1 : (p : R) ∣ (x ^ (p ^ (f * (k + 1)))) ^ (p ^ f) - x ^ (p ^ f) :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have h2 := dvd_add h1 h
    rwa [sub_add_sub_cancel] at h2

theorem frobFix_common {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    ∃ f : ℕ, 0 < f ∧ (p : R) ∣ x ^ (p ^ f) - x ∧ (p : R) ∣ y ^ (p ^ f) - y := by
  obtain ⟨f1, hf1, h1⟩ := hx
  obtain ⟨f2, hf2, h2⟩ := hy
  refine ⟨f1 * f2, Nat.mul_pos hf1 hf2, ?_, ?_⟩
  · have h := frobFix_iter h1 (f2 - 1)
    rwa [Nat.sub_add_cancel hf2] at h
  · have h := frobFix_iter h2 (f1 - 1)
    rwa [Nat.sub_add_cancel hf1, mul_comm] at h

theorem frobFix_mul {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) : FrobFix p (x * y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have e : (x * y) ^ (p ^ f) - x * y = x ^ (p ^ f) * (y ^ (p ^ f) - y) + y * (x ^ (p ^ f) - x) := by
    ring
  rw [e]
  exact dvd_add (dvd_mul_of_dvd_right h2 _) (dvd_mul_of_dvd_right h1 _)

private theorem frobFix_add_lemma (hp : p.Prime) (x y : R) (n : ℕ) :
    (p : R) ∣ (x + y) ^ (p ^ n) - (x ^ (p ^ n) + y ^ (p ^ n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hA : (p : R) ∣ ((x + y) ^ (p ^ n)) ^ p - (x ^ (p ^ n) + y ^ (p ^ n)) ^ p :=
      dvd_trans ih (sub_dvd_pow_sub_pow _ _ _)
    have hB : (p : R) ∣ (x ^ (p ^ n) + y ^ (p ^ n)) ^ p - ((x ^ (p ^ n)) ^ p + (y ^ (p ^ n)) ^ p) := by
      rw [add_pow_prime_eq hp, add_sub_cancel_left]
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
    have e : ∀ a : R, a ^ (p ^ (n + 1)) = (a ^ (p ^ n)) ^ p := fun a => by
      rw [pow_succ, pow_mul]
    rw [e, e, e]
    have h := dvd_add hA hB
    rwa [sub_add_sub_cancel] at h

theorem frobFix_add (hp : p.Prime) {x y : R} (hx : FrobFix p x) (hy : FrobFix p y) :
    FrobFix p (x + y) := by
  obtain ⟨f, hf, h1, h2⟩ := frobFix_common hx hy
  refine ⟨f, hf, ?_⟩
  have h3 := frobFix_add_lemma hp x y f
  have e : (x + y) ^ (p ^ f) - (x + y) =
      ((x + y) ^ (p ^ f) - (x ^ (p ^ f) + y ^ (p ^ f))) + (x ^ (p ^ f) - x) + (y ^ (p ^ f) - y) := by
    ring
  rw [e]
  exact dvd_add (dvd_add h3 h1) h2

theorem frobFix_neg_one (hp : p.Prime) : FrobFix p (-1 : R) := by
  refine ⟨1, one_pos, ?_⟩
  rcases hp.eq_two_or_odd' with rfl | hodd
  · rw [show (-1 : R) ^ (2 ^ 1) - -1 = ((2 : ℕ) : R) by push_cast; ring]
  · rw [pow_one, hodd.neg_one_pow, sub_self]
    exact dvd_zero _

theorem frobFix_neg (hp : p.Prime) {x : R} (hx : FrobFix p x) : FrobFix p (-x) := by
  simpa using frobFix_mul (frobFix_neg_one (R := R) hp) hx

theorem frobFix_zero (hp : p.Prime) : FrobFix p (0 : R) :=
  ⟨1, one_pos, by rw [pow_one, zero_pow hp.ne_zero, sub_zero]; exact dvd_zero _⟩

theorem frobFix_one : FrobFix p (1 : R) :=
  ⟨1, one_pos, by simp⟩

theorem frobFix_root (hp : p.Prime) {x : R} {n : ℕ} (hn : 0 < n) (hpn : ¬ p ∣ n)
    (hx : x ^ n = 1) : FrobFix p x := by
  have hcop : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hpn
  have htot : p ^ n.totient % n = 1 % n := Nat.ModEq.pow_totient hcop
  refine ⟨n.totient, Nat.totient_pos.2 hn, ?_⟩
  have key : ∀ m, x ^ m = x ^ (m % n) := fun m => by
    conv_lhs => rw [← Nat.mod_add_div m n, pow_add, pow_mul, hx, one_pow, mul_one]
  have hx' : x ^ (p ^ n.totient) = x := by
    rw [key, htot, ← key, pow_one]
  rw [hx', sub_self]
  exact dvd_zero _

def frobFixSubring (R : Type*) [CommRing R] (hp : p.Prime) : Subring R where
  carrier := {x | FrobFix p x}
  mul_mem' := frobFix_mul
  one_mem' := frobFix_one
  add_mem' := frobFix_add hp
  zero_mem' := frobFix_zero hp
  neg_mem' := frobFix_neg hp

end General

variable (l : ℕ) [Fact l.Prime]

theorem rmu_frob (x : ℂ_[l]) (hx : x ∈ Rmu l) :
    ∃ f : ℕ, 0 < f ∧ ∃ r ∈ Rmu l, x ^ (l ^ f) - x = (l : ℂ_[l]) * r := by
  have hp : l.Prime := Fact.out
  have key : ∀ (y : ℂ_[l]) (hy : y ∈ Subring.closure (muP l)), FrobFix l (⟨y, hy⟩ : Rmu l) := by
    intro y hy
    induction hy using Subring.closure_induction with
    | mem z hz =>
      obtain ⟨n, hn, hln, hzn⟩ := hz
      exact frobFix_root hp hn hln (Subtype.ext (by simpa using hzn))
    | zero => exact frobFix_zero hp
    | one => exact frobFix_one
    | add a b ha' hb' ha hb =>
      have e : (⟨a + b, Subring.add_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ + ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_add hp ha hb
    | neg a ha' ha =>
      have e : (⟨-a, Subring.neg_mem _ ha'⟩ : Rmu l) = -⟨a, ha'⟩ := Subtype.ext (by simp)
      rw [e]
      exact frobFix_neg hp ha
    | mul a b ha' hb' ha hb =>
      have e : (⟨a * b, Subring.mul_mem _ ha' hb'⟩ : Rmu l) = ⟨a, ha'⟩ * ⟨b, hb'⟩ :=
        Subtype.ext (by simp)
      rw [e]
      exact frobFix_mul ha hb
  obtain ⟨f, hf, r, hr⟩ := key x hx
  refine ⟨f, hf, r, r.2, ?_⟩
  have h := congrArg Subtype.val hr
  simpa using h

end ReciprocityTheory.ChartRestriction.L1
