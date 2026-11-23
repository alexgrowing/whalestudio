import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.ConstantCoeffSurjective
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.AcrisKummerUnits.GaloisTwistIdentitySection
set_option backward.isDefEq.respectTransparency false
open CategoryTheory GroundTheory.PAdicHodge CrystallineSemistableComparison CrystallineSemistableComparison.PAlg

namespace GlobalTheory.CompanionTheory.FrobFixed

open Polynomial in

theorem sum_one_sub_pow {l : ℕ} [Fact l.Prime] [NeZero l] :
    ∑ c : ZMod l, (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) = 1 := by
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by
    have := hl.two_le
    omega
  rw [← sub_eq_zero]
  refine Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' _ Finset.univ (fun a _ => ?_) ?_
  · have key : ∀ c : ZMod l, (1 - (a - c) ^ (l - 1) : ZMod l) = if a = c then 1 else 0 := fun c => by
      split_ifs with h
      · rw [h, sub_self, zero_pow hl1, sub_zero]
      · rw [ZMod.pow_card_sub_one_eq_one (sub_ne_zero.2 h), sub_self]
    simp only [eval_sub, eval_finset_sum, eval_one, eval_pow, eval_X, eval_C, key]
    simp
  · have hdeg : ∀ c : ZMod l, natDegree (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) ≤ l - 1 := fun c => by
      refine (natDegree_sub_le _ _).trans (max_le (by simp) ?_)
      refine natDegree_pow_le.trans ?_
      rw [natDegree_X_sub_C, mul_one]
    have h1 : natDegree (∑ c : ZMod l, (1 - (X - C c) ^ (l - 1) : (ZMod l)[X]) - 1) ≤ l - 1 := by
      refine (natDegree_sub_le _ _).trans (max_le ?_ (by simp))
      exact natDegree_sum_le_of_forall_le _ _ fun c _ => hdeg c
    rw [Finset.card_univ, ZMod.card]
    have := hl.two_le
    omega

theorem exists_idempotents {R : Type*} [CommRing R] {l : ℕ} [Fact l.Prime] [NeZero l]
    (hR : (l : R) = 0) (x : R) (hx : x ^ l = x) :
    ∃ e : ZMod l → R, CompleteOrthogonalIdempotents e ∧ ∀ c, e c * (x - (c.val : R)) = 0 := by
  rcases subsingleton_or_nontrivial R with h | h
  · exact ⟨0, ⟨⟨fun _ => Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _⟩,
      Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  have hl : l.Prime := Fact.out
  have hl1 : l - 1 ≠ 0 := by
    have := hl.two_le
    omega
  haveI : CharP R l := (CharP.charP_iff_prime_eq_zero hl).2 hR
  letI : Algebra (ZMod l) R := ZMod.algebra R l
  have hφ : ∀ c : ZMod l, (c.val : R) = algebraMap (ZMod l) R c := fun c => by
    rw [← map_natCast (algebraMap (ZMod l) R), ZMod.natCast_zmod_val]
  have hpow : ∀ c : ZMod l, (x - algebraMap (ZMod l) R c) ^ l = x - algebraMap (ZMod l) R c := fun c => by
    rw [sub_pow_char, hx, ← map_pow, ZMod.pow_card]
  obtain ⟨e, he⟩ : ∃ e : ZMod l → R, ∀ c, e c = 1 - (x - algebraMap (ZMod l) R c) ^ (l - 1) := ⟨_, fun _ => rfl⟩
  have hann : ∀ c, e c * (x - algebraMap (ZMod l) R c) = 0 := fun c => by
    have h1 : (x - algebraMap (ZMod l) R c) ^ (l - 1) * (x - algebraMap (ZMod l) R c)
        = x - algebraMap (ZMod l) R c := by
      rw [← pow_succ, Nat.sub_add_cancel hl.one_le, hpow]
    rw [he, sub_mul, one_mul, h1, sub_self]
  have hlin : ∀ c d, e c * (x - algebraMap (ZMod l) R d) = e c * algebraMap (ZMod l) R (c - d) := fun c d => by
    have h1 : x - algebraMap (ZMod l) R d
        = (x - algebraMap (ZMod l) R c) + algebraMap (ZMod l) R (c - d) := by
      rw [map_sub]; ring
    rw [h1, mul_add, hann, zero_add]
  have hmul : ∀ c d k, e c * (x - algebraMap (ZMod l) R d) ^ k
      = e c * algebraMap (ZMod l) R ((c - d) ^ k) := fun c d k => by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ, ← mul_assoc, ih, mul_right_comm, hlin, mul_assoc, ← map_mul, pow_succ']
  refine ⟨e, ⟨⟨fun c => ?_, fun c d hcd => ?_⟩, ?_⟩, fun c => by rw [hφ, hann]⟩
  · change e c * e c = e c
    have h1 : e c * e c = e c * (1 - (x - algebraMap (ZMod l) R c) ^ (l - 1)) := congrArg (e c * ·) (he c)
    rw [h1, mul_sub, mul_one, hmul, sub_self, zero_pow hl1, map_zero, mul_zero, sub_zero]
  · change e c * e d = 0
    rw [he d, mul_sub, mul_one, hmul, ZMod.pow_card_sub_one_eq_one (sub_ne_zero.2 hcd), map_one, mul_one,
      sub_self]
  · have h1 := congrArg (Polynomial.aeval x) (sum_one_sub_pow (l := l))
    simp only [map_sum, map_sub, map_one, map_pow, Polynomial.aeval_X, Polynomial.aeval_C] at h1
    rw [← h1]
    exact Finset.sum_congr rfl fun c _ => he c

theorem fix_one : ∀ {l : ℕ} [Fact l.Prime] (A : PAlg l) (x : A.A), x ^ l = x → ∃ e : ZMod l → A.A, (haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩; CompleteOrthogonalIdempotents e ∧ ∀ c, e c * (x - (c.val : A.A)) = 0) := by
  intro l _ A x hx
  haveI : NeZero l := ⟨(Fact.out : l.Prime).ne_zero⟩
  exact exists_idempotents A.natCast_l x hx

end GlobalTheory.CompanionTheory.FrobFixed
