import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrKIsometricAndOneSubSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntWeightsCompatibleRootsOfUnityLevelsStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage.Values

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K : FinExt l)

theorem zeta_pow (m i : ℕ) : P.ζQ (m + i) ^ (l ^ i) = P.ζQ m := by
  induction i with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, P.ζQ_succ, ih]

theorem cycVal_single {s e j : ℕ} (hj : 1 ≤ j) (hjs : j ≤ s) (μ : ℕ → ℤ) (V : Om l)
    (hμ : ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a = if i = j then V else 0)
    (x : ↥(K0 K)) :
    cycVal P K s e (fun a => (μ a : ↥(K0 K)) * x) 0 =
      (l : Om l) ^ (e * (s - j)) * (((frK P K ^ (s - j)) x : ↥(K0 K)) : Om l) * V := by
  have key : ∀ i ∈ Finset.range s,
      ∑ a ∈ primeTo l s, (((frK P K ^ i) ((μ a : ↥(K0 K)) * x) : ↥(K0 K)) : Om l) *
        P.ζQ s ^ (a * l ^ i) =
      (((frK P K ^ i) x : ↥(K0 K)) : Om l) * (if s - i = j then V else 0) := by
    intro i hi
    have hi' := Finset.mem_range.mp hi
    rw [← hμ (s - i) (by omega) (by omega), Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    have hz : P.ζQ s ^ (l ^ i) = P.ζQ (s - i) := by
      have := zeta_pow P (s - i) i
      rwa [Nat.sub_add_cancel hi'.le] at this
    rw [map_mul, map_intCast, mul_comm a, pow_mul, hz]
    push_cast
    ring
  unfold cycVal
  rw [Finset.sum_congr rfl fun i hi => by rw [key i hi], Finset.sum_eq_single (s - j)]
  · rw [if_pos (by omega)]
    simp [mul_assoc]
  · intro i hi hne
    have hi' := Finset.mem_range.mp hi
    rw [if_neg (by omega)]
    simp
  · intro h
    exact absurd (Finset.mem_range.mpr (by omega)) h

theorem cycVal_add (s e : ℕ) (f g : ℕ → ↥(K0 K)) (d : ↥(K0 K)) :
    cycVal P K s e (fun a => f a + g a) d =
      cycVal P K s e f 0 + cycVal P K s e g 0 + (l : Om l) ^ (s * e) * (d : Om l) := by
  unfold cycVal
  simp only [map_add, IntermediateField.coe_add, add_mul, Finset.sum_add_distrib, mul_add,
    IntermediateField.coe_zero, mul_zero, add_zero]

theorem exists_pre (k : ℕ) (y : ↥(K0 K)) :
    ∃ x : ↥(K0 K), (frK P K ^ k) x = y ∧ ‖(x : Om l)‖ = ‖(y : Om l)‖ := by
  induction k generalizing y with
  | zero => exact ⟨y, rfl, rfl⟩
  | succ k ih =>
    obtain ⟨z, rfl⟩ := (P.PD K).σ_bij.2 y
    obtain ⟨x, hx, hn⟩ := ih z
    refine ⟨x, ?_, ?_⟩
    · rw [pow_succ', AlgHom.mul_apply, hx]
    · rw [hn]
      exact ((GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1 z).symm

theorem norm_int_mul {z : ℤ} {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((z : ↥(K0 K)) * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  push_cast
  rw [norm_mul]
  exact mul_le_one₀ (IsUltrametricDist.norm_intCast_le_one _ z) (norm_nonneg _) hx

theorem norm_pow_mul (k : ℕ) {x : ↥(K0 K)} (hx : ‖(x : Om l)‖ ≤ 1) :
    ‖(((l : ↥(K0 K)) ^ k * x : ↥(K0 K)) : Om l)‖ ≤ 1 := by
  have := norm_int_mul K (z := (l : ℤ) ^ k) hx
  simpa using this

theorem sum_zeta : ∑ r ∈ Finset.Ico 1 l, P.ζQ 1 ^ r = -1 := by
  have h1 : P.ζQ 1 ^ l = 1 := (P.ζQ_succ 0).trans P.ζQ_zero
  have h2 := mul_geom_sum (P.ζQ 1) l
  rw [h1, sub_self, mul_eq_zero] at h2
  have h3 := h2.resolve_left (sub_ne_zero.mpr P.ζQ_one)
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Fact.out : l.Prime).pos] at h3
  simp only [pow_zero, zero_add] at h3
  linear_combination h3

theorem exists_minus_one {s : ℕ} (hs : 1 ≤ s) : ∃ ν : ℕ → ℤ,
    ∑ a ∈ primeTo l s, ν a = ((l : ℤ) - 1) * (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (ν a : Om l) * P.ζQ i ^ a =
        if i = 1 then -(l : Om l) ^ (s - 1) else 0 := by
  have h : ∀ r : ℕ, ∃ μ : ℕ → ℤ, r ∈ Finset.Ico 1 l →
      (∑ a ∈ primeTo l s, μ a = (l : ℤ) ^ (s - 1) ∧ ∀ i, 1 ≤ i → i ≤ s →
      ∑ a ∈ primeTo l s, (μ a : Om l) * P.ζQ i ^ a =
        if i = 1 then (l : Om l) ^ (s - 1) * P.ζQ 1 ^ r else 0) := by
    intro r
    by_cases hr : r ∈ Finset.Ico 1 l
    · have hr' := Finset.mem_Ico.mp hr
      obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s 1 r le_rfl hs
        (Nat.not_dvd_of_pos_of_lt hr'.1 hr'.2)
      exact ⟨μ, fun _ => ⟨by simpa using h1, by simpa using h2⟩⟩
    · exact ⟨0, fun h => absurd h hr⟩
  choose μ hμ using h
  refine ⟨fun a => ∑ r ∈ Finset.Ico 1 l, μ r a, ?_, fun i hi his => ?_⟩
  · rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).1, Finset.sum_const,
      Nat.card_Ico, nsmul_eq_mul, Nat.cast_sub (Fact.out : l.Prime).one_lt.le, Nat.cast_one]
  · push_cast
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.sum_congr rfl fun r hr => (hμ r hr).2 i hi his]
    split_ifs
    · rw [← Finset.mul_sum, sum_zeta]
      ring
    · simp

theorem exists_cycVal_eq (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l) (s e j n : ℕ)
    (hj : 1 ≤ j) (hjs : j ≤ s) (hn : ¬ l ∣ n) (c : Om l) (hc : c ∈ K0 K) (hc1 : ‖c‖ ≤ 1) :
    ∃ (lam : ℕ → ↥(K0 K)) (d : ↥(K0 K)), (∀ a, ‖(lam a : Om l)‖ ≤ 1) ∧ ‖(d : Om l)‖ ≤ 1 ∧
      d - (l : ↥(K0 K)) ^ e * frK P K d = (frK P K ^ s) (∑ a ∈ primeTo l s, lam a) ∧
      cycVal P K s e lam d = (l : Om l) ^ ((e + 1) * (s - 1)) * (c * P.ζQ j ^ n) := by
  obtain ⟨c, rfl⟩ : ∃ c' : ↥(K0 K), (c' : Om l) = c := ⟨⟨c, hc⟩, rfl⟩
  obtain ⟨μ, h1, h2⟩ := GlobalTheory.T.exists_int_weights_compatibleRootsOfUnity_levels l P.ζQ P.ζQ_zero P.ζQ_one P.ζQ_succ s j n hj hjs hn
  by_cases hj1 : j = 1
  · subst hj1
    simp only [if_true] at h1 h2
    obtain ⟨ν, g1, g2⟩ := exists_minus_one P hjs
    obtain ⟨d, hd, hdc⟩ := (GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).2 (e + 1) (by omega) (frK P K c)
      (by rw [(GlobalTheory.T.norm_frK_eq_and_exists_sub_pow_smul_frK_eq l P K).1]; exact hc1)
    obtain ⟨x, hx, hxn⟩ := exists_pre P K (s - 1) c
    obtain ⟨y, hy, hyn⟩ := exists_pre P K (s - 1) ((l : ↥(K0 K)) ^ e * d)
    obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at *
    refine ⟨fun a => (μ a : ↥(K0 K)) * x + (ν a : ↥(K0 K)) * y, (l : ↥(K0 K)) ^ t * d,
      fun a => ?_, norm_pow_mul K t hd, ?_, ?_⟩
    · rw [IntermediateField.coe_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le
        (norm_int_mul K (hxn ▸ hc1)) (norm_int_mul K (hyn ▸ norm_pow_mul K e hd)))
    · rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, ← Int.cast_sum,
        ← Int.cast_sum, h1, g1, pow_succ' (frK P K), AlgHom.mul_apply, map_add, map_mul, map_mul,
        map_mul, map_intCast, map_intCast, hx, hy]
      simp only [map_add, map_mul, map_pow, map_natCast, map_intCast]
      push_cast
      linear_combination (l : ↥(K0 K)) ^ t * hdc
    · rw [cycVal_add, cycVal_single P K le_rfl hjs μ _ h2, cycVal_single P K le_rfl hjs ν _ g2]
      simp only [Nat.add_sub_cancel]
      rw [hx, hy]
      push_cast
      ring
  · simp only [if_neg hj1] at h1 h2
    obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
    obtain ⟨t, rfl⟩ : ∃ t, s = k + 2 + t := ⟨s - (k + 2), by omega⟩
    obtain ⟨x, hx, hxn⟩ := exists_pre P K t ((l : ↥(K0 K)) ^ ((e + 1) * k + e) * c)
    refine ⟨fun a => (μ a : ↥(K0 K)) * x, 0,
      fun a => norm_int_mul K (hxn ▸ norm_pow_mul K _ hc1), by simp, ?_, ?_⟩
    · rw [← Finset.sum_mul, ← Int.cast_sum, h1]
      simp
    · rw [cycVal_single P K hj hjs μ _ h2, Nat.add_sub_cancel_left, hx,
        show k + 2 + t - 1 = k + t + 1 by omega]
      push_cast
      ring

end GlobalTheory.ExpImage.Values
