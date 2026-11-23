import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisIncl
import Development.AbelianVarietyTheory.CrystallinePeriods.RingBasics

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.LogAdd

open Polynomial

theorem one_add_mul_derivative_trunc {R : Type} [CommRing R] (n : ℕ) (u : R[X]) (hu : u ^ n = 0) :
    (1 + u) * derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (n.factorial : R[X]) * derivative u := by
  have h1 : derivative (∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-u) ^ k) * ((n.factorial : R[X]) * derivative u) := by
    rw [derivative_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hd : (k + 1) ∣ n.factorial :=
      Nat.dvd_factorial (Nat.succ_pos k) (Finset.mem_range.1 hk)
    have hc : ((n.factorial / (k + 1) : ℕ) : R[X]) * ((k : R[X]) + 1) = (n.factorial : R[X]) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → R[X]) (Nat.div_mul_cancel hd)
    have hs : derivative ((-1 : R[X]) ^ k) = 0 := by
      rcases neg_one_pow_eq_or R[X] k with h | h <;> simp [h]
    rw [derivative_mul, derivative_mul, hs, derivative_natCast, derivative_pow_succ, ← hc, neg_pow u]
    simp only [map_add, map_natCast, map_one]
    ring
  have h2 : (1 + u) * ∑ k ∈ Finset.range n, (-u) ^ k = 1 := by
    have := mul_neg_geom_sum (-u) n
    rw [sub_neg_eq_add, neg_pow u, hu, mul_zero, sub_zero] at this
    exact this
  rw [h1, ← mul_assoc, h2, one_mul]

theorem trunc_add {R : Type} [CommRing R] (hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : R)) (n : ℕ)
    (I : Ideal R) (hI : I ^ n = ⊥) (a b : R) (ha : a ∈ I) (hb : b ∈ I) :
    (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * (a + b + a * b) ^ (k + 1)) =
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * a ^ (k + 1)) +
      (∑ k ∈ Finset.range n, (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R) * b ^ (k + 1)) := by
  let F : R[X] → R[X] := fun u => ∑ k ∈ Finset.range n,
      (-1) ^ k * ((n.factorial / (k + 1) : ℕ) : R[X]) * u ^ (k + 1)
  let J : Ideal R[X] := I.map (C : R →+* R[X])
  have hJ : ∀ u ∈ J, u ^ n = 0 := by
    intro u hu
    have := Ideal.pow_mem_pow hu n
    rwa [← Ideal.map_pow, hI, Ideal.map_bot, Ideal.mem_bot] at this
  set s : R[X] := C a * X with hs
  set t : R[X] := C b * X with ht
  have hsJ : s ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ ha)
  have htJ : t ∈ J := J.mul_mem_right _ (Ideal.mem_map_of_mem _ hb)
  have huJ : s + t + s * t ∈ J := J.add_mem (J.add_mem hsJ htJ) (J.mul_mem_right _ hsJ)
  have e1 : (1 + s) * derivative (F s) = _ := one_add_mul_derivative_trunc n s (hJ _ hsJ)
  have e2 : (1 + t) * derivative (F t) = _ := one_add_mul_derivative_trunc n t (hJ _ htJ)
  have e3 : (1 + (s + t + s * t)) * derivative (F (s + t + s * t)) = _ :=
    one_add_mul_derivative_trunc n _ (hJ _ huJ)
  have hunit : IsUnit (1 + (s + t + s * t)) := IsNilpotent.isUnit_one_add ⟨n, hJ _ huJ⟩
  have hD : derivative (F (s + t + s * t) - F s - F t) = 0 := by
    apply hunit.mul_left_cancel
    rw [derivative_add, derivative_add, derivative_mul (f := s) (g := t)] at e3
    rw [derivative_sub, derivative_sub]
    linear_combination e3 - (1 + t) * e1 - (1 + s) * e2
  have hC : F (s + t + s * t) - F s - F t = C ((F (s + t + s * t) - F s - F t).coeff 0) := by
    ext k
    cases k with
    | zero => simp only [coeff_C_zero]
    | succ k =>
      have h := congrArg (fun p => coeff p k) hD
      simp only [coeff_derivative, coeff_zero] at h
      rw [coeff_C_succ]
      have hu : IsUnit ((k : R) + 1) := by exact_mod_cast hR (k + 1) (Nat.succ_ne_zero k)
      exact (hu.mul_left_eq_zero).1 h
  have h0 : (F (s + t + s * t) - F s - F t).coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    simp [F, hs, ht, eval_finsetSum]
  rw [h0, map_zero] at hC
  have h1 := congrArg (eval 1) hC
  simp only [F, hs, ht, eval_sub, eval_finsetSum, eval_mul, eval_pow, eval_neg, eval_one,
    eval_natCast, eval_add, eval_C, eval_X, mul_one, eval_zero] at h1
  linear_combination h1

theorem tm_sub_one_mem (l : ℕ) [Fact l.Prime] (e : Per.Fl l) (he : e.untilt = 1) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) ∈ Per.kerP l := by
  apply GlobalTheory.RingIface.alg_mem_kerP
  simp [he]

theorem map_mul_sub_one {M A B : Type} [Monoid M] [CommRing A] [CommRing B] (g : M →* A)
    (f : A →+* B) (e e' : M) :
    f (g (e * e') - 1) = f (g e - 1) + f (g e' - 1) + f (g e - 1) * f (g e' - 1) := by
  simp only [map_sub, map_mul, map_one]
  ring

theorem tm_mul_sub_one (l : ℕ) [Fact l.Prime] (e e' : Per.Fl l) :
    algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm (e * e') - 1) =
      algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) +
        algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) *
          algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) :=
  map_mul_sub_one (WittVector.teichmuller l) _ e e'

theorem log_add : ∀ (l : ℕ) [Fact l.Prime], ∀ (e e' : Per.Fl l) (y y' z : Per.BdRp l),
    e.untilt = 1 → e'.untilt = 1 → Per.IsLog l e y → Per.IsLog l e' y' →
      Per.IsLog l (e * e') z → z = y + y' := by
  intro l _ e e' y y' z he he' hy hy' hz
  refine GlobalTheory.RingIface.ev_ext l _ _ fun n => ?_
  let q : Per.AinfP l →+* Per.AinfP l ⧸ Per.kerP l ^ n := Ideal.Quotient.mk _
  have hR : ∀ m : ℕ, m ≠ 0 → IsUnit (m : Per.AinfP l ⧸ Per.kerP l ^ n) := fun m hm => by
    have := (GlobalTheory.RingBasics.isUnit_nat l m hm).map q
    rwa [map_natCast] at this
  apply (hR _ n.factorial_ne_zero).mul_left_cancel
  rw [map_add, mul_add, GlobalTheory.CrisIncl.factorial_mul_ev l e y he hy n,
    GlobalTheory.CrisIncl.factorial_mul_ev l e' y' he' hy' n,
    GlobalTheory.CrisIncl.factorial_mul_ev l _ z (by rw [map_mul, he, he', mul_one]) hz n]
  have hI : ((Per.kerP l).map q) ^ n = ⊥ := by
    rw [← Ideal.map_pow]
    exact Ideal.map_quotient_self _
  have key := trunc_add hR n _ hI _ _ (Ideal.mem_map_of_mem q (tm_sub_one_mem l e he))
    (Ideal.mem_map_of_mem q (tm_sub_one_mem l e' he'))
  rw [tm_mul_sub_one]
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e - 1) = a at key ⊢
  generalize algebraMap (Per.Ainf l) (Per.AinfP l) (Per.tm e' - 1) = b at key ⊢
  change q _ = q _ + q _
  simp only [map_sum, map_mul, map_pow, map_neg, map_one, map_natCast, map_add]
  exact key

end GlobalTheory.MemLoc.LogAdd
