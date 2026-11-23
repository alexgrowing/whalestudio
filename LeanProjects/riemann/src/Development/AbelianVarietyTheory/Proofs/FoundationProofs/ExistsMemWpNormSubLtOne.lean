import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPowSubOneNormLtOne

open Formalism.MainNotions

namespace GlobalTheory.ResidueRoot

open Polynomial

variable {p : ℕ} [hp : Fact p.Prime]

def ball (p : ℕ) [Fact p.Prime] : Subring ℂ_[p] where
  carrier := {x | ‖x‖ ≤ 1}
  mul_mem' := fun {a b} ha hb => by
    show ‖a * b‖ ≤ 1
    rw [norm_mul]; exact mul_le_one₀ ha (norm_nonneg _) hb
  one_mem' := by show ‖(1 : ℂ_[p])‖ ≤ 1; simp
  add_mem' := fun {a b} ha hb => (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha hb)
  zero_mem' := by show ‖(0 : ℂ_[p])‖ ≤ 1; simp
  neg_mem' := fun {a} ha => by show ‖-a‖ ≤ 1; rw [norm_neg]; exact ha

theorem norm_p_lt_one : ‖(p : ℂ_[p])‖ < 1 := by
  have h := PadicComplex.norm_extends' p (p : ℚ_[p])
  have h2 : ‖(p : ℚ_[p])‖ < 1 := Padic.norm_p_lt_one
  rw [← h] at h2
  simpa using h2

theorem norm_add_lt_one {a b : ℂ_[p]} (ha : ‖a‖ < 1) (hb : ‖b‖ < 1) : ‖a + b‖ < 1 :=
  (IsUltrametricDist.norm_add_le_max a b).trans_lt (max_lt ha hb)

theorem sub_one_lt_of_pow_p {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p - 1‖ < 1) : ‖y - 1‖ < 1 := by
  let Y : ball p := ⟨y, hy⟩
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp.out (Y - 1) 1
  have hr' := congrArg (fun t : ball p => (t : ℂ_[p])) hr
  simp only [sub_add_cancel, one_pow, mul_one] at hr'
  push_cast at hr'
  have hz : ‖y - 1‖ ≤ 1 := (Y - 1).2
  have hrr : ‖(r : ℂ_[p])‖ ≤ 1 := r.2
  have e : (y - 1) ^ p = (y ^ p - 1) + -((p : ℂ_[p]) * (y - 1) * r) := by
    have : (Y : ℂ_[p]) = y := rfl
    rw [this] at hr'
    rw [hr']; ring
  have h2 : ‖(y - 1) ^ p‖ < 1 := by
    rw [e]
    refine norm_add_lt_one h ?_
    rw [norm_neg, norm_mul, norm_mul, mul_assoc]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) norm_p_lt_one
      (mul_le_one₀ hz (norm_nonneg _) hrr)
  rw [norm_pow] at h2
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hp.out.ne_zero).1 h2

theorem sub_one_lt_of_pow_p_pow (k : ℕ) {y : ℂ_[p]} (hy : ‖y‖ ≤ 1) (h : ‖y ^ p ^ k - 1‖ < 1) :
    ‖y - 1‖ < 1 := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply sub_one_lt_of_pow_p
    · rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy
    · rwa [← pow_mul, ← pow_succ]

theorem exists_root {x : ℂ_[p]} {m : ℕ} (hm : 0 < m) (h : ‖x ^ m - 1‖ < 1) :
    ∃ ζ : ℂ_[p], ζ ^ m = 1 ∧ ‖x - ζ‖ < 1 := by
  haveI : NeZero m := ⟨hm.ne'⟩
  obtain ⟨ξ, hξ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot ℂ_[p] m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm hξ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  rw [e, norm_prod] at h
  by_contra hc
  push Not at hc
  refine absurd h (not_lt.2 ?_)
  exact Finset.prod_induction _ (fun r : ℝ => 1 ≤ r) (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb)
    le_rfl fun ζ hζ => hc ζ ((mem_nthRootsFinset hm _).1 hζ)

theorem exists_pow_alg (x : PadicAlgCl p) (hx : ‖x‖ = 1) : ∃ n, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  first
  | exact @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one
  | (apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> assumption)
  | (intros; apply @_root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.PowerNearOneNorm.exists_pow_sub_one_norm_lt_one ..)

end GlobalTheory.ResidueRoot

namespace GlobalTheory

open ResidueRoot

theorem exists_mem_Wp_norm_sub_lt_one (p : ℕ) [hp : Fact p.Prime] (x : ℂ_[p]) (hx : ‖x‖ ≤ 1) :
    ∃ w ∈ GL3Theta.Wp p, ‖x - w‖ < 1 := by
  obtain ⟨y, hy⟩ := Metric.denseRange_iff.1
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) x 1 one_pos
  rw [dist_eq_norm] at hy
  have hy1 : ‖(y : ℂ_[p])‖ ≤ 1 := by
    have : (y : ℂ_[p]) = x + -(x - y) := by ring
    rw [this]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rw [norm_neg]; exact hy.le))
  rcases hy1.lt_or_eq with h | h
  · refine ⟨0, zero_mem _, ?_⟩
    have := norm_add_lt_one hy h
    simpa using this
  · obtain ⟨n, hn, hyn⟩ := exists_pow_alg y (by rwa [PadicComplex.norm_extends] at h)
    obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' p hp.out.ne_one
    have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero p))
    have h3 : ‖((y : ℂ_[p]) ^ m) ^ p ^ k - 1‖ < 1 := by
      rw [← PadicComplex.norm_extends, PadicComplex.coe_eq, map_sub, map_pow, map_one,
        ← PadicComplex.coe_eq] at hyn
      rwa [← pow_mul, mul_comm]
    have h4 := sub_one_lt_of_pow_p_pow k
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hy1) h3
    obtain ⟨ζ, hζ, h5⟩ := exists_root hm0 h4
    refine ⟨ζ, Subring.le_topologicalClosure _ (Subring.subset_closure
      ⟨m, hm0, ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm, hζ⟩), ?_⟩
    have := norm_add_lt_one hy h5
    simpa using this

end GlobalTheory
